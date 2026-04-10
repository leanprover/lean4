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
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
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
LEAN_EXPORT uint8_t l_String_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_String_Range_includes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_String_Range_overlaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Range_bsize(lean_object*);
LEAN_EXPORT lean_object* l_String_Range_bsize___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_isLitKind___closed__0 = (const lean_object*)&l_Lean_isLitKind___closed__0_value;
static const lean_ctor_object l_Lean_isLitKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_isLitKind___closed__1 = (const lean_object*)&l_Lean_isLitKind___closed__1_value;
static const lean_string_object l_Lean_isLitKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_isLitKind___closed__2 = (const lean_object*)&l_Lean_isLitKind___closed__2_value;
static const lean_ctor_object l_Lean_isLitKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_isLitKind___closed__3 = (const lean_object*)&l_Lean_isLitKind___closed__3_value;
static const lean_string_object l_Lean_isLitKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_isLitKind___closed__4 = (const lean_object*)&l_Lean_isLitKind___closed__4_value;
static const lean_ctor_object l_Lean_isLitKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_isLitKind___closed__5 = (const lean_object*)&l_Lean_isLitKind___closed__5_value;
static const lean_string_object l_Lean_isLitKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_isLitKind___closed__6 = (const lean_object*)&l_Lean_isLitKind___closed__6_value;
static const lean_ctor_object l_Lean_isLitKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_isLitKind___closed__7 = (const lean_object*)&l_Lean_isLitKind___closed__7_value;
static const lean_string_object l_Lean_isLitKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_isLitKind___closed__8 = (const lean_object*)&l_Lean_isLitKind___closed__8_value;
static const lean_ctor_object l_Lean_isLitKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reuse stopped:\n"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " !=\n"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_0),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_1),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__3(lean_object*);
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_identComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_identComponents___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_identComponents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_getAtomVal___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_identComponents___closed__1 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__1_value;
static const lean_string_object l_Lean_Syntax_identComponents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l_Lean_Syntax_identComponents___closed__2 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__2_value;
static const lean_string_object l_Lean_Syntax_identComponents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Syntax.identComponents"};
static const lean_object* l_Lean_Syntax_identComponents___closed__3 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__3_value;
static const lean_string_object l_Lean_Syntax_identComponents___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Syntax_identComponents___closed__4 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__4_value;
static lean_once_cell_t l_Lean_Syntax_identComponents___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents___closed__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t);
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
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_Stack_matches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_Stack_matches___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_Stack_matches___closed__0 = (const lean_object*)&l_Lean_Syntax_Stack_matches___closed__0_value;
static const lean_array_object l_Lean_Syntax_Stack_matches___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_Stack_matches___closed__1 = (const lean_object*)&l_Lean_Syntax_Stack_matches___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object*, lean_object*);
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
lean_object* v_start_95_; lean_object* v_stop_96_; lean_object* v_start_97_; lean_object* v_stop_98_; uint8_t v___x_99_; 
v_start_95_ = lean_ctor_get(v_x_93_, 0);
v_stop_96_ = lean_ctor_get(v_x_93_, 1);
v_start_97_ = lean_ctor_get(v_x_94_, 0);
v_stop_98_ = lean_ctor_get(v_x_94_, 1);
v___x_99_ = lean_nat_dec_eq(v_start_95_, v_start_97_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_eq(v_stop_96_, v_stop_98_);
return v___x_100_;
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
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_lt(v_pos_121_, v_stop_124_);
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_le(v_pos_121_, v_stop_124_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object* v_r_128_, lean_object* v_pos_129_, lean_object* v_includeStop_130_){
_start:
{
uint8_t v_includeStop_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_includeStop_boxed_131_ = lean_unbox(v_includeStop_130_);
v_res_132_ = l_Lean_Syntax_Range_contains(v_r_128_, v_pos_129_, v_includeStop_boxed_131_);
lean_dec(v_pos_129_);
lean_dec_ref(v_r_128_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_includes(lean_object* v_super_134_, lean_object* v_sub_135_, uint8_t v_includeSuperStop_136_, uint8_t v_includeSubStop_137_){
_start:
{
lean_object* v_start_138_; lean_object* v_stop_139_; lean_object* v_start_140_; lean_object* v_stop_141_; uint8_t v___y_143_; uint8_t v___x_147_; uint8_t v___y_149_; 
v_start_138_ = lean_ctor_get(v_super_134_, 0);
v_stop_139_ = lean_ctor_get(v_super_134_, 1);
v_start_140_ = lean_ctor_get(v_sub_135_, 0);
v_stop_141_ = lean_ctor_get(v_sub_135_, 1);
v___x_147_ = lean_nat_dec_le(v_start_138_, v_start_140_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
if (v_includeSuperStop_136_ == 0)
{
v___y_149_ = v_includeSuperStop_136_;
goto v___jp_148_;
}
else
{
if (v_includeSubStop_137_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_stop_139_, v___x_150_);
v___x_152_ = lean_nat_dec_le(v_stop_141_, v___x_151_);
lean_dec(v___x_151_);
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 0;
v___y_149_ = v___x_153_;
goto v___jp_148_;
}
}
}
v___jp_142_:
{
if (v___y_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_le(v_stop_141_, v_stop_139_);
return v___x_144_;
}
else
{
if (v_includeSubStop_137_ == 0)
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v_stop_141_, v_stop_139_);
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_lt(v_stop_141_, v_stop_139_);
return v___x_146_;
}
}
}
v___jp_148_:
{
if (v_includeSuperStop_136_ == 0)
{
v___y_143_ = v___x_147_;
goto v___jp_142_;
}
else
{
v___y_143_ = v___y_149_;
goto v___jp_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_154_, lean_object* v_sub_155_, lean_object* v_includeSuperStop_156_, lean_object* v_includeSubStop_157_){
_start:
{
uint8_t v_includeSuperStop_boxed_158_; uint8_t v_includeSubStop_boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_includeSuperStop_boxed_158_ = lean_unbox(v_includeSuperStop_156_);
v_includeSubStop_boxed_159_ = lean_unbox(v_includeSubStop_157_);
v_res_160_ = l_Lean_Syntax_Range_includes(v_super_154_, v_sub_155_, v_includeSuperStop_boxed_158_, v_includeSubStop_boxed_159_);
lean_dec_ref(v_sub_155_);
lean_dec_ref(v_super_154_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_String_Range_includes(lean_object* v_super_162_, lean_object* v_sub_163_, uint8_t v_includeSuperStop_164_, uint8_t v_includeSubStop_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_Lean_Syntax_Range_includes(v_super_162_, v_sub_163_, v_includeSuperStop_164_, v_includeSubStop_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_String_Range_includes___boxed(lean_object* v_super_167_, lean_object* v_sub_168_, lean_object* v_includeSuperStop_169_, lean_object* v_includeSubStop_170_){
_start:
{
uint8_t v_includeSuperStop_boxed_171_; uint8_t v_includeSubStop_boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_includeSuperStop_boxed_171_ = lean_unbox(v_includeSuperStop_169_);
v_includeSubStop_boxed_172_ = lean_unbox(v_includeSubStop_170_);
v_res_173_ = l_String_Range_includes(v_super_167_, v_sub_168_, v_includeSuperStop_boxed_171_, v_includeSubStop_boxed_172_);
lean_dec_ref(v_sub_168_);
lean_dec_ref(v_super_167_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_175_, lean_object* v_second_176_, uint8_t v_includeFirstStop_177_, uint8_t v_includeSecondStop_178_){
_start:
{
uint8_t v___y_180_; 
if (v_includeFirstStop_177_ == 0)
{
lean_object* v_start_187_; lean_object* v_stop_188_; uint8_t v___x_189_; 
v_start_187_ = lean_ctor_get(v_second_176_, 0);
v_stop_188_ = lean_ctor_get(v_first_175_, 1);
v___x_189_ = lean_nat_dec_lt(v_start_187_, v_stop_188_);
v___y_180_ = v___x_189_;
goto v___jp_179_;
}
else
{
lean_object* v_start_190_; lean_object* v_stop_191_; uint8_t v___x_192_; 
v_start_190_ = lean_ctor_get(v_second_176_, 0);
v_stop_191_ = lean_ctor_get(v_first_175_, 1);
v___x_192_ = lean_nat_dec_le(v_start_190_, v_stop_191_);
v___y_180_ = v___x_192_;
goto v___jp_179_;
}
v___jp_179_:
{
if (v___y_180_ == 0)
{
return v___y_180_;
}
else
{
if (v_includeSecondStop_178_ == 0)
{
lean_object* v_start_181_; lean_object* v_stop_182_; uint8_t v___x_183_; 
v_start_181_ = lean_ctor_get(v_first_175_, 0);
v_stop_182_ = lean_ctor_get(v_second_176_, 1);
v___x_183_ = lean_nat_dec_lt(v_start_181_, v_stop_182_);
return v___x_183_;
}
else
{
lean_object* v_start_184_; lean_object* v_stop_185_; uint8_t v___x_186_; 
v_start_184_ = lean_ctor_get(v_first_175_, 0);
v_stop_185_ = lean_ctor_get(v_second_176_, 1);
v___x_186_ = lean_nat_dec_le(v_start_184_, v_stop_185_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object* v_first_193_, lean_object* v_second_194_, lean_object* v_includeFirstStop_195_, lean_object* v_includeSecondStop_196_){
_start:
{
uint8_t v_includeFirstStop_boxed_197_; uint8_t v_includeSecondStop_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_includeFirstStop_boxed_197_ = lean_unbox(v_includeFirstStop_195_);
v_includeSecondStop_boxed_198_ = lean_unbox(v_includeSecondStop_196_);
v_res_199_ = l_Lean_Syntax_Range_overlaps(v_first_193_, v_second_194_, v_includeFirstStop_boxed_197_, v_includeSecondStop_boxed_198_);
lean_dec_ref(v_second_194_);
lean_dec_ref(v_first_193_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_String_Range_overlaps(lean_object* v_first_201_, lean_object* v_second_202_, uint8_t v_includeFirstStop_203_, uint8_t v_includeSecondStop_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_Syntax_Range_overlaps(v_first_201_, v_second_202_, v_includeFirstStop_203_, v_includeSecondStop_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_Range_overlaps___boxed(lean_object* v_first_206_, lean_object* v_second_207_, lean_object* v_includeFirstStop_208_, lean_object* v_includeSecondStop_209_){
_start:
{
uint8_t v_includeFirstStop_boxed_210_; uint8_t v_includeSecondStop_boxed_211_; uint8_t v_res_212_; lean_object* v_r_213_; 
v_includeFirstStop_boxed_210_ = lean_unbox(v_includeFirstStop_208_);
v_includeSecondStop_boxed_211_ = lean_unbox(v_includeSecondStop_209_);
v_res_212_ = l_String_Range_overlaps(v_first_206_, v_second_207_, v_includeFirstStop_boxed_210_, v_includeSecondStop_boxed_211_);
lean_dec_ref(v_second_207_);
lean_dec_ref(v_first_206_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_214_){
_start:
{
lean_object* v_start_215_; lean_object* v_stop_216_; lean_object* v___x_217_; 
v_start_215_ = lean_ctor_get(v_r_214_, 0);
v_stop_216_ = lean_ctor_get(v_r_214_, 1);
v___x_217_ = lean_nat_sub(v_stop_216_, v_start_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Syntax_Range_bsize(v_r_218_);
lean_dec_ref(v_r_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_String_Range_bsize(lean_object* v_r_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Syntax_Range_bsize(v_r_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_String_Range_bsize___boxed(lean_object* v_r_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_String_Range_bsize(v_r_222_);
lean_dec_ref(v_r_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_224_, lean_object* v_x_225_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v_leading_226_; lean_object* v_pos_227_; lean_object* v_endPos_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_leading_226_ = lean_ctor_get(v_x_225_, 0);
v_pos_227_ = lean_ctor_get(v_x_225_, 1);
v_endPos_228_ = lean_ctor_get(v_x_225_, 3);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v_x_225_, 2);
lean_dec(v_unused_236_);
v___x_230_ = v_x_225_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_endPos_228_);
lean_inc(v_pos_227_);
lean_inc(v_leading_226_);
lean_dec(v_x_225_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 2, v_trailing_224_);
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_leading_226_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_pos_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_trailing_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_endPos_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
else
{
lean_dec_ref(v_trailing_224_);
return v_x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_237_, lean_object* v_info_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_SourceInfo_getPos_x3f(v_info_238_, v_canonicalOnly_237_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
return v___x_240_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_242_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref(v___x_239_);
v___x_242_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_238_, v_canonicalOnly_237_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; 
lean_dec(v_val_241_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_val_244_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v___x_242_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_242_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_val_241_);
lean_ctor_set(v___x_248_, 1, v_val_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_253_, lean_object* v_info_254_){
_start:
{
uint8_t v_canonicalOnly_boxed_255_; lean_object* v_res_256_; 
v_canonicalOnly_boxed_255_ = lean_unbox(v_canonicalOnly_253_);
v_res_256_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_255_, v_info_254_);
lean_dec(v_info_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_257_, lean_object* v_info_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_SourceInfo_getPos_x3f(v_info_258_, v_canonicalOnly_257_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_260_; 
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v___x_262_; 
v_val_261_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_val_261_);
lean_dec_ref(v___x_259_);
v___x_262_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_258_, v_canonicalOnly_257_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; 
lean_dec(v_val_261_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_val_264_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v___x_262_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_val_264_);
lean_dec(v___x_262_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_val_261_);
lean_ctor_set(v___x_268_, 1, v_val_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_273_, lean_object* v_info_274_){
_start:
{
uint8_t v_canonicalOnly_boxed_275_; lean_object* v_res_276_; 
v_canonicalOnly_boxed_275_ = lean_unbox(v_canonicalOnly_273_);
v_res_276_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_275_, v_info_274_);
lean_dec(v_info_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_277_){
_start:
{
switch(lean_obj_tag(v_x_277_))
{
case 0:
{
lean_object* v_pos_278_; lean_object* v_endPos_279_; uint8_t v___x_280_; lean_object* v___x_281_; 
v_pos_278_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_pos_278_);
v_endPos_279_ = lean_ctor_get(v_x_277_, 3);
lean_inc(v_endPos_279_);
lean_dec_ref(v_x_277_);
v___x_280_ = 0;
v___x_281_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_281_, 0, v_pos_278_);
lean_ctor_set(v___x_281_, 1, v_endPos_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*2, v___x_280_);
return v___x_281_;
}
case 1:
{
lean_object* v_pos_282_; lean_object* v_endPos_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_pos_282_ = lean_ctor_get(v_x_277_, 0);
v_endPos_283_ = lean_ctor_get(v_x_277_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v_x_277_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_endPos_283_);
lean_inc(v_pos_282_);
lean_dec(v_x_277_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
uint8_t v___x_287_; lean_object* v___x_289_; 
v___x_287_ = 0;
if (v_isShared_286_ == 0)
{
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_pos_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_endPos_283_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*2, v___x_287_);
return v___x_289_;
}
}
}
default: 
{
return v_x_277_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
switch(lean_obj_tag(v_x_292_))
{
case 0:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v_leading_294_; lean_object* v_pos_295_; lean_object* v_trailing_296_; lean_object* v_endPos_297_; lean_object* v_leading_298_; lean_object* v_pos_299_; lean_object* v_trailing_300_; lean_object* v_endPos_301_; uint8_t v___x_302_; 
v_leading_294_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_leading_294_);
v_pos_295_ = lean_ctor_get(v_x_292_, 1);
lean_inc(v_pos_295_);
v_trailing_296_ = lean_ctor_get(v_x_292_, 2);
lean_inc_ref(v_trailing_296_);
v_endPos_297_ = lean_ctor_get(v_x_292_, 3);
lean_inc(v_endPos_297_);
lean_dec_ref(v_x_292_);
v_leading_298_ = lean_ctor_get(v_x_293_, 0);
lean_inc_ref(v_leading_298_);
v_pos_299_ = lean_ctor_get(v_x_293_, 1);
lean_inc(v_pos_299_);
v_trailing_300_ = lean_ctor_get(v_x_293_, 2);
lean_inc_ref(v_trailing_300_);
v_endPos_301_ = lean_ctor_get(v_x_293_, 3);
lean_inc(v_endPos_301_);
lean_dec_ref(v_x_293_);
v___x_302_ = l_Substring_Raw_beq(v_leading_294_, v_leading_298_);
if (v___x_302_ == 0)
{
lean_dec(v_endPos_301_);
lean_dec_ref(v_trailing_300_);
lean_dec(v_pos_299_);
lean_dec(v_endPos_297_);
lean_dec_ref(v_trailing_296_);
lean_dec(v_pos_295_);
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_pos_295_, v_pos_299_);
lean_dec(v_pos_299_);
lean_dec(v_pos_295_);
if (v___x_303_ == 0)
{
lean_dec(v_endPos_301_);
lean_dec_ref(v_trailing_300_);
lean_dec(v_endPos_297_);
lean_dec_ref(v_trailing_296_);
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = l_Substring_Raw_beq(v_trailing_296_, v_trailing_300_);
if (v___x_304_ == 0)
{
lean_dec(v_endPos_301_);
lean_dec(v_endPos_297_);
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = lean_nat_dec_eq(v_endPos_297_, v_endPos_301_);
lean_dec(v_endPos_301_);
lean_dec(v_endPos_297_);
return v___x_305_;
}
}
}
}
else
{
uint8_t v___x_306_; 
lean_dec_ref(v_x_292_);
lean_dec(v_x_293_);
v___x_306_ = 0;
return v___x_306_;
}
}
case 1:
{
if (lean_obj_tag(v_x_293_) == 1)
{
lean_object* v_pos_307_; lean_object* v_endPos_308_; uint8_t v_canonical_309_; lean_object* v_pos_310_; lean_object* v_endPos_311_; uint8_t v_canonical_312_; uint8_t v___x_313_; 
v_pos_307_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_pos_307_);
v_endPos_308_ = lean_ctor_get(v_x_292_, 1);
lean_inc(v_endPos_308_);
v_canonical_309_ = lean_ctor_get_uint8(v_x_292_, sizeof(void*)*2);
lean_dec_ref(v_x_292_);
v_pos_310_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_pos_310_);
v_endPos_311_ = lean_ctor_get(v_x_293_, 1);
lean_inc(v_endPos_311_);
v_canonical_312_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*2);
lean_dec_ref(v_x_293_);
v___x_313_ = lean_nat_dec_eq(v_pos_307_, v_pos_310_);
lean_dec(v_pos_310_);
lean_dec(v_pos_307_);
if (v___x_313_ == 0)
{
lean_dec(v_endPos_311_);
lean_dec(v_endPos_308_);
return v___x_313_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = lean_nat_dec_eq(v_endPos_308_, v_endPos_311_);
lean_dec(v_endPos_311_);
lean_dec(v_endPos_308_);
if (v___x_314_ == 0)
{
return v___x_314_;
}
else
{
if (v_canonical_309_ == 0)
{
if (v_canonical_312_ == 0)
{
return v___x_314_;
}
else
{
return v_canonical_309_;
}
}
else
{
return v_canonical_312_;
}
}
}
}
else
{
uint8_t v___x_315_; 
lean_dec_ref(v_x_292_);
lean_dec(v_x_293_);
v___x_315_ = 0;
return v___x_315_;
}
}
default: 
{
if (lean_obj_tag(v_x_293_) == 2)
{
uint8_t v___x_316_; 
v___x_316_ = 1;
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
lean_dec(v_x_293_);
v___x_317_ = 0;
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_318_, v_x_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_324_, lean_object* v_a_325_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_326_, lean_object* v_info_327_, lean_object* v_val_328_, lean_object* v_a_329_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_330_, lean_object* v_info_331_, lean_object* v_val_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_330_, v_info_331_, v_val_332_, v_a_333_);
lean_dec_ref(v_val_332_);
lean_dec(v_info_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_335_, lean_object* v_info_336_, lean_object* v_rawVal_337_, lean_object* v_val_338_, lean_object* v_preresolved_339_, lean_object* v_a_340_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_341_, lean_object* v_info_342_, lean_object* v_rawVal_343_, lean_object* v_val_344_, lean_object* v_preresolved_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_341_, v_info_342_, v_rawVal_343_, v_val_344_, v_preresolved_345_, v_a_346_);
lean_dec(v_preresolved_345_);
lean_dec(v_val_344_);
lean_dec_ref(v_rawVal_343_);
lean_dec(v_info_342_);
return v_res_347_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object* v_k_363_){
_start:
{
uint8_t v___y_365_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_373_ = lean_name_eq(v_k_363_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_375_ = lean_name_eq(v_k_363_, v___x_374_);
v___y_365_ = v___x_375_;
goto v___jp_364_;
}
else
{
v___y_365_ = v___x_373_;
goto v___jp_364_;
}
v___jp_364_:
{
if (v___y_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_367_ = lean_name_eq(v_k_363_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_369_ = lean_name_eq(v_k_363_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_371_ = lean_name_eq(v_k_363_, v___x_370_);
return v___x_371_;
}
else
{
return v___x_369_;
}
}
else
{
return v___x_367_;
}
}
else
{
return v___y_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_isLitKind(v_k_376_);
lean_dec(v_k_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_379_){
_start:
{
lean_object* v_kind_380_; 
v_kind_380_ = lean_ctor_get(v_n_379_, 1);
lean_inc(v_kind_380_);
return v_kind_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_SyntaxNode_getKind(v_n_381_);
lean_dec(v_n_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_383_, lean_object* v_fn_384_){
_start:
{
lean_object* v_args_385_; lean_object* v___x_386_; 
v_args_385_ = lean_ctor_get(v_n_383_, 2);
lean_inc_ref(v_args_385_);
lean_dec(v_n_383_);
v___x_386_ = lean_apply_1(v_fn_384_, v_args_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_387_, lean_object* v_n_388_, lean_object* v_fn_389_){
_start:
{
lean_object* v_args_390_; lean_object* v___x_391_; 
v_args_390_ = lean_ctor_get(v_n_388_, 2);
lean_inc_ref(v_args_390_);
lean_dec(v_n_388_);
v___x_391_ = lean_apply_1(v_fn_389_, v_args_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_392_){
_start:
{
lean_object* v_args_393_; lean_object* v___x_394_; 
v_args_393_ = lean_ctor_get(v_n_392_, 2);
v___x_394_ = lean_array_get_size(v_args_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_SyntaxNode_getNumArgs(v_n_395_);
lean_dec(v_n_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_397_, lean_object* v_i_398_){
_start:
{
lean_object* v_args_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_args_399_ = lean_ctor_get(v_n_397_, 2);
v___x_400_ = lean_box(0);
v___x_401_ = lean_array_get_borrowed(v___x_400_, v_args_399_, v_i_398_);
lean_inc(v___x_401_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_402_, lean_object* v_i_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_SyntaxNode_getArg(v_n_402_, v_i_403_);
lean_dec(v_i_403_);
lean_dec(v_n_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_405_){
_start:
{
lean_object* v_args_406_; 
v_args_406_ = lean_ctor_get(v_n_405_, 2);
lean_inc_ref(v_args_406_);
return v_args_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_SyntaxNode_getArgs(v_n_407_);
lean_dec(v_n_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_409_, lean_object* v_fn_410_){
_start:
{
lean_object* v_info_411_; lean_object* v_kind_412_; lean_object* v_args_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_info_411_ = lean_ctor_get(v_n_409_, 0);
v_kind_412_ = lean_ctor_get(v_n_409_, 1);
v_args_413_ = lean_ctor_get(v_n_409_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v_n_409_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_n_409_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_args_413_);
lean_inc(v_kind_412_);
lean_inc(v_info_411_);
lean_dec(v_n_409_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_apply_1(v_fn_410_, v_args_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 2, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_info_411_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_kind_412_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_422_, lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
if (lean_obj_tag(v_x_423_) == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 1;
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
}
else
{
if (lean_obj_tag(v_x_423_) == 0)
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
else
{
lean_object* v_val_427_; lean_object* v_val_428_; uint8_t v___x_429_; 
v_val_427_ = lean_ctor_get(v_x_422_, 0);
v_val_428_ = lean_ctor_get(v_x_423_, 0);
v___x_429_ = l_Lean_Syntax_instBEqRange_beq(v_val_427_, v_val_428_);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec(v_x_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
if (lean_obj_tag(v_x_435_) == 0)
{
uint8_t v___x_436_; 
v___x_436_ = 1;
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
}
else
{
if (lean_obj_tag(v_x_435_) == 0)
{
uint8_t v___x_438_; 
v___x_438_ = 0;
return v___x_438_;
}
else
{
lean_object* v_head_439_; lean_object* v_tail_440_; lean_object* v_head_441_; lean_object* v_tail_442_; uint8_t v___x_443_; 
v_head_439_ = lean_ctor_get(v_x_434_, 0);
v_tail_440_ = lean_ctor_get(v_x_434_, 1);
v_head_441_ = lean_ctor_get(v_x_435_, 0);
v_tail_442_ = lean_ctor_get(v_x_435_, 1);
v___x_443_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_439_, v_head_441_);
if (v___x_443_ == 0)
{
return v___x_443_;
}
else
{
v_x_434_ = v_tail_440_;
v_x_435_ = v_tail_442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_445_, v_x_446_);
lean_dec(v_x_446_);
lean_dec(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
switch(lean_obj_tag(v_x_449_))
{
case 0:
{
if (lean_obj_tag(v_x_450_) == 0)
{
uint8_t v___x_451_; 
v___x_451_ = 1;
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
lean_dec(v_x_450_);
v___x_452_ = 0;
return v___x_452_;
}
}
case 1:
{
if (lean_obj_tag(v_x_450_) == 1)
{
lean_object* v_info_453_; lean_object* v_kind_454_; lean_object* v_args_455_; lean_object* v_info_456_; lean_object* v_kind_457_; lean_object* v_args_458_; uint8_t v___y_460_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_info_453_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_info_453_);
v_kind_454_ = lean_ctor_get(v_x_449_, 1);
lean_inc(v_kind_454_);
v_args_455_ = lean_ctor_get(v_x_449_, 2);
lean_inc_ref(v_args_455_);
lean_dec_ref(v_x_449_);
v_info_456_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_info_456_);
v_kind_457_ = lean_ctor_get(v_x_450_, 1);
lean_inc(v_kind_457_);
v_args_458_ = lean_ctor_get(v_x_450_, 2);
lean_inc_ref(v_args_458_);
lean_dec_ref(v_x_450_);
v___x_465_ = 0;
v___x_466_ = l_Lean_SourceInfo_getRange_x3f(v___x_465_, v_info_453_);
lean_dec(v_info_453_);
v___x_467_ = l_Lean_SourceInfo_getRange_x3f(v___x_465_, v_info_456_);
lean_dec(v_info_456_);
v___x_468_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_466_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_466_);
if (v___x_468_ == 0)
{
lean_dec(v_kind_457_);
lean_dec(v_kind_454_);
v___y_460_ = v___x_468_;
goto v___jp_459_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = lean_name_eq(v_kind_454_, v_kind_457_);
lean_dec(v_kind_457_);
lean_dec(v_kind_454_);
v___y_460_ = v___x_469_;
goto v___jp_459_;
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
lean_dec_ref(v_args_458_);
lean_dec_ref(v_args_455_);
return v___y_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_array_get_size(v_args_455_);
v___x_462_ = lean_array_get_size(v_args_458_);
v___x_463_ = lean_nat_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec_ref(v_args_458_);
lean_dec_ref(v_args_455_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_args_455_, v_args_458_, v___x_461_);
lean_dec_ref(v_args_458_);
lean_dec_ref(v_args_455_);
return v___x_464_;
}
}
}
}
else
{
uint8_t v___x_470_; 
lean_dec_ref(v_x_449_);
lean_dec(v_x_450_);
v___x_470_ = 0;
return v___x_470_;
}
}
case 2:
{
if (lean_obj_tag(v_x_450_) == 2)
{
lean_object* v_info_471_; lean_object* v_val_472_; lean_object* v_info_473_; lean_object* v_val_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_info_471_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_info_471_);
v_val_472_ = lean_ctor_get(v_x_449_, 1);
lean_inc_ref(v_val_472_);
lean_dec_ref(v_x_449_);
v_info_473_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_info_473_);
v_val_474_ = lean_ctor_get(v_x_450_, 1);
lean_inc_ref(v_val_474_);
lean_dec_ref(v_x_450_);
v___x_475_ = 0;
v___x_476_ = l_Lean_SourceInfo_getRange_x3f(v___x_475_, v_info_471_);
lean_dec(v_info_471_);
v___x_477_ = l_Lean_SourceInfo_getRange_x3f(v___x_475_, v_info_473_);
lean_dec(v_info_473_);
v___x_478_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_476_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v___x_476_);
if (v___x_478_ == 0)
{
lean_dec_ref(v_val_474_);
lean_dec_ref(v_val_472_);
return v___x_478_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = lean_string_dec_eq(v_val_472_, v_val_474_);
lean_dec_ref(v_val_474_);
lean_dec_ref(v_val_472_);
return v___x_479_;
}
}
else
{
uint8_t v___x_480_; 
lean_dec_ref(v_x_449_);
lean_dec(v_x_450_);
v___x_480_ = 0;
return v___x_480_;
}
}
default: 
{
if (lean_obj_tag(v_x_450_) == 3)
{
lean_object* v_info_481_; lean_object* v_rawVal_482_; lean_object* v_val_483_; lean_object* v_preresolved_484_; lean_object* v_info_485_; lean_object* v_rawVal_486_; lean_object* v_val_487_; lean_object* v_preresolved_488_; uint8_t v___y_490_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_info_481_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_info_481_);
v_rawVal_482_ = lean_ctor_get(v_x_449_, 1);
lean_inc_ref(v_rawVal_482_);
v_val_483_ = lean_ctor_get(v_x_449_, 2);
lean_inc(v_val_483_);
v_preresolved_484_ = lean_ctor_get(v_x_449_, 3);
lean_inc(v_preresolved_484_);
lean_dec_ref(v_x_449_);
v_info_485_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_info_485_);
v_rawVal_486_ = lean_ctor_get(v_x_450_, 1);
lean_inc_ref(v_rawVal_486_);
v_val_487_ = lean_ctor_get(v_x_450_, 2);
lean_inc(v_val_487_);
v_preresolved_488_ = lean_ctor_get(v_x_450_, 3);
lean_inc(v_preresolved_488_);
lean_dec_ref(v_x_450_);
v___x_493_ = 0;
v___x_494_ = l_Lean_SourceInfo_getRange_x3f(v___x_493_, v_info_481_);
lean_dec(v_info_481_);
v___x_495_ = l_Lean_SourceInfo_getRange_x3f(v___x_493_, v_info_485_);
lean_dec(v_info_485_);
v___x_496_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_494_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v___x_494_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_rawVal_486_);
lean_dec_ref(v_rawVal_482_);
v___y_490_ = v___x_496_;
goto v___jp_489_;
}
else
{
uint8_t v___x_497_; 
v___x_497_ = l_Substring_Raw_beq(v_rawVal_482_, v_rawVal_486_);
v___y_490_ = v___x_497_;
goto v___jp_489_;
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
lean_dec(v_preresolved_488_);
lean_dec(v_val_487_);
lean_dec(v_preresolved_484_);
lean_dec(v_val_483_);
return v___y_490_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = lean_name_eq(v_val_483_, v_val_487_);
lean_dec(v_val_487_);
lean_dec(v_val_483_);
if (v___x_491_ == 0)
{
lean_dec(v_preresolved_488_);
lean_dec(v_preresolved_484_);
return v___x_491_;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_484_, v_preresolved_488_);
lean_dec(v_preresolved_488_);
lean_dec(v_preresolved_484_);
return v___x_492_;
}
}
}
}
else
{
uint8_t v___x_498_; 
lean_dec_ref(v_x_449_);
lean_dec(v_x_450_);
v___x_498_ = 0;
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object* v_xs_499_, lean_object* v_ys_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_zero_502_; uint8_t v_isZero_503_; 
v_zero_502_ = lean_unsigned_to_nat(0u);
v_isZero_503_ = lean_nat_dec_eq(v_x_501_, v_zero_502_);
if (v_isZero_503_ == 1)
{
lean_dec(v_x_501_);
return v_isZero_503_;
}
else
{
lean_object* v_one_504_; lean_object* v_n_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_one_504_ = lean_unsigned_to_nat(1u);
v_n_505_ = lean_nat_sub(v_x_501_, v_one_504_);
lean_dec(v_x_501_);
v___x_506_ = lean_array_fget_borrowed(v_xs_499_, v_n_505_);
v___x_507_ = lean_array_fget_borrowed(v_ys_500_, v_n_505_);
lean_inc(v___x_507_);
lean_inc(v___x_506_);
v___x_508_ = l_Lean_Syntax_structRangeEq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v_n_505_);
return v___x_508_;
}
else
{
v_x_501_ = v_n_505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object* v_xs_510_, lean_object* v_ys_511_, lean_object* v_x_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_510_, v_ys_511_, v_x_512_);
lean_dec_ref(v_ys_511_);
lean_dec_ref(v_xs_510_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Lean_Syntax_structRangeEq(v_x_515_, v_x_516_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_xs_519_, lean_object* v_ys_520_, lean_object* v_hsz_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_519_, v_ys_520_, v_x_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_xs_525_, lean_object* v_ys_526_, lean_object* v_hsz_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_525_, v_ys_526_, v_hsz_527_, v_x_528_, v_x_529_);
lean_dec_ref(v_ys_526_);
lean_dec_ref(v_xs_525_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_532_, lean_object* v_x_533_){
_start:
{
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_534_, lean_object* v_x_535_){
_start:
{
uint8_t v___x_207__boxed_536_; uint8_t v_res_537_; lean_object* v_r_538_; 
v___x_207__boxed_536_ = lean_unbox(v___x_534_);
v_res_537_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_207__boxed_536_, v_x_535_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_548_, lean_object* v_stx1_549_, lean_object* v_stx2_550_){
_start:
{
uint8_t v___x_551_; uint8_t v___x_552_; 
lean_inc(v_stx2_550_);
lean_inc(v_stx1_549_);
v___x_551_ = l_Lean_Syntax_structRangeEq(v_stx1_549_, v_stx2_550_);
v___x_552_ = 1;
if (v___x_551_ == 0)
{
lean_object* v_map_553_; lean_object* v___x_554_; lean_object* v___f_555_; uint8_t v___y_557_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_map_553_ = lean_ctor_get(v_opts_548_, 0);
v___x_554_ = lean_box(v___x_551_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_555_, 0, v___x_554_);
v___x_572_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_553_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
v___y_557_ = v___x_551_;
goto v___jp_556_;
}
else
{
lean_object* v_val_574_; 
v_val_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_val_574_);
lean_dec_ref(v___x_573_);
if (lean_obj_tag(v_val_574_) == 1)
{
uint8_t v_v_575_; 
v_v_575_ = lean_ctor_get_uint8(v_val_574_, 0);
lean_dec_ref(v_val_574_);
v___y_557_ = v_v_575_;
goto v___jp_556_;
}
else
{
lean_dec(v_val_574_);
v___y_557_ = v___x_551_;
goto v___jp_556_;
}
}
v___jp_556_:
{
if (v___y_557_ == 0)
{
lean_dec_ref(v___f_555_);
lean_dec(v_stx2_550_);
lean_dec(v_stx1_549_);
return v___x_551_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_558_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_559_ = lean_box(0);
v___x_560_ = l_Lean_Syntax_formatStx(v_stx1_549_, v___x_559_, v___x_552_);
v___x_561_ = l_Std_Format_defWidth;
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = l_Std_Format_pretty(v___x_560_, v___x_561_, v___x_562_, v___x_562_);
v___x_564_ = lean_string_append(v___x_558_, v___x_563_);
lean_dec_ref(v___x_563_);
v___x_565_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_566_ = lean_string_append(v___x_564_, v___x_565_);
v___x_567_ = l_Lean_Syntax_formatStx(v_stx2_550_, v___x_559_, v___x_552_);
v___x_568_ = l_Std_Format_pretty(v___x_567_, v___x_561_, v___x_562_, v___x_562_);
v___x_569_ = lean_string_append(v___x_566_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = lean_dbg_trace(v___x_569_, v___f_555_);
v___x_571_ = lean_unbox(v___x_570_);
lean_dec(v___x_570_);
return v___x_571_;
}
}
}
else
{
lean_dec(v_stx2_550_);
lean_dec(v_stx1_549_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_576_, lean_object* v_stx1_577_, lean_object* v_stx2_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_576_, v_stx1_577_, v_stx2_578_);
lean_dec_ref(v_opts_576_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
switch(lean_obj_tag(v_x_581_))
{
case 0:
{
if (lean_obj_tag(v_x_582_) == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 1;
return v___x_583_;
}
else
{
uint8_t v___x_584_; 
lean_dec(v_x_582_);
v___x_584_ = 0;
return v___x_584_;
}
}
case 1:
{
if (lean_obj_tag(v_x_582_) == 1)
{
lean_object* v_info_585_; lean_object* v_kind_586_; lean_object* v_args_587_; lean_object* v_info_588_; lean_object* v_kind_589_; lean_object* v_args_590_; uint8_t v___y_592_; uint8_t v___x_597_; 
v_info_585_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_info_585_);
v_kind_586_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_kind_586_);
v_args_587_ = lean_ctor_get(v_x_581_, 2);
lean_inc_ref(v_args_587_);
lean_dec_ref(v_x_581_);
v_info_588_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_info_588_);
v_kind_589_ = lean_ctor_get(v_x_582_, 1);
lean_inc(v_kind_589_);
v_args_590_ = lean_ctor_get(v_x_582_, 2);
lean_inc_ref(v_args_590_);
lean_dec_ref(v_x_582_);
v___x_597_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_585_, v_info_588_);
if (v___x_597_ == 0)
{
lean_dec(v_kind_589_);
lean_dec(v_kind_586_);
v___y_592_ = v___x_597_;
goto v___jp_591_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = lean_name_eq(v_kind_586_, v_kind_589_);
lean_dec(v_kind_589_);
lean_dec(v_kind_586_);
v___y_592_ = v___x_598_;
goto v___jp_591_;
}
v___jp_591_:
{
if (v___y_592_ == 0)
{
lean_dec_ref(v_args_590_);
lean_dec_ref(v_args_587_);
return v___y_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_array_get_size(v_args_587_);
v___x_594_ = lean_array_get_size(v_args_590_);
v___x_595_ = lean_nat_dec_eq(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_args_590_);
lean_dec_ref(v_args_587_);
return v___x_595_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_587_, v_args_590_, v___x_593_);
lean_dec_ref(v_args_590_);
lean_dec_ref(v_args_587_);
return v___x_596_;
}
}
}
}
else
{
uint8_t v___x_599_; 
lean_dec_ref(v_x_581_);
lean_dec(v_x_582_);
v___x_599_ = 0;
return v___x_599_;
}
}
case 2:
{
if (lean_obj_tag(v_x_582_) == 2)
{
lean_object* v_info_600_; lean_object* v_val_601_; lean_object* v_info_602_; lean_object* v_val_603_; uint8_t v___x_604_; 
v_info_600_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_info_600_);
v_val_601_ = lean_ctor_get(v_x_581_, 1);
lean_inc_ref(v_val_601_);
lean_dec_ref(v_x_581_);
v_info_602_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_info_602_);
v_val_603_ = lean_ctor_get(v_x_582_, 1);
lean_inc_ref(v_val_603_);
lean_dec_ref(v_x_582_);
v___x_604_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_600_, v_info_602_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_val_603_);
lean_dec_ref(v_val_601_);
return v___x_604_;
}
else
{
uint8_t v___x_605_; 
v___x_605_ = lean_string_dec_eq(v_val_601_, v_val_603_);
lean_dec_ref(v_val_603_);
lean_dec_ref(v_val_601_);
return v___x_605_;
}
}
else
{
uint8_t v___x_606_; 
lean_dec_ref(v_x_581_);
lean_dec(v_x_582_);
v___x_606_ = 0;
return v___x_606_;
}
}
default: 
{
if (lean_obj_tag(v_x_582_) == 3)
{
lean_object* v_info_607_; lean_object* v_rawVal_608_; lean_object* v_val_609_; lean_object* v_preresolved_610_; lean_object* v_info_611_; lean_object* v_rawVal_612_; lean_object* v_val_613_; lean_object* v_preresolved_614_; uint8_t v___y_616_; uint8_t v___x_619_; 
v_info_607_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_info_607_);
v_rawVal_608_ = lean_ctor_get(v_x_581_, 1);
lean_inc_ref(v_rawVal_608_);
v_val_609_ = lean_ctor_get(v_x_581_, 2);
lean_inc(v_val_609_);
v_preresolved_610_ = lean_ctor_get(v_x_581_, 3);
lean_inc(v_preresolved_610_);
lean_dec_ref(v_x_581_);
v_info_611_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_info_611_);
v_rawVal_612_ = lean_ctor_get(v_x_582_, 1);
lean_inc_ref(v_rawVal_612_);
v_val_613_ = lean_ctor_get(v_x_582_, 2);
lean_inc(v_val_613_);
v_preresolved_614_ = lean_ctor_get(v_x_582_, 3);
lean_inc(v_preresolved_614_);
lean_dec_ref(v_x_582_);
v___x_619_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_607_, v_info_611_);
if (v___x_619_ == 0)
{
lean_dec_ref(v_rawVal_612_);
lean_dec_ref(v_rawVal_608_);
v___y_616_ = v___x_619_;
goto v___jp_615_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = l_Substring_Raw_beq(v_rawVal_608_, v_rawVal_612_);
v___y_616_ = v___x_620_;
goto v___jp_615_;
}
v___jp_615_:
{
if (v___y_616_ == 0)
{
lean_dec(v_preresolved_614_);
lean_dec(v_val_613_);
lean_dec(v_preresolved_610_);
lean_dec(v_val_609_);
return v___y_616_;
}
else
{
uint8_t v___x_617_; 
v___x_617_ = lean_name_eq(v_val_609_, v_val_613_);
lean_dec(v_val_613_);
lean_dec(v_val_609_);
if (v___x_617_ == 0)
{
lean_dec(v_preresolved_614_);
lean_dec(v_preresolved_610_);
return v___x_617_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_610_, v_preresolved_614_);
lean_dec(v_preresolved_614_);
lean_dec(v_preresolved_610_);
return v___x_618_;
}
}
}
}
else
{
uint8_t v___x_621_; 
lean_dec_ref(v_x_581_);
lean_dec(v_x_582_);
v___x_621_ = 0;
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_622_, lean_object* v_ys_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_zero_625_; uint8_t v_isZero_626_; 
v_zero_625_ = lean_unsigned_to_nat(0u);
v_isZero_626_ = lean_nat_dec_eq(v_x_624_, v_zero_625_);
if (v_isZero_626_ == 1)
{
lean_dec(v_x_624_);
return v_isZero_626_;
}
else
{
lean_object* v_one_627_; lean_object* v_n_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_one_627_ = lean_unsigned_to_nat(1u);
v_n_628_ = lean_nat_sub(v_x_624_, v_one_627_);
lean_dec(v_x_624_);
v___x_629_ = lean_array_fget_borrowed(v_xs_622_, v_n_628_);
v___x_630_ = lean_array_fget_borrowed(v_ys_623_, v_n_628_);
lean_inc(v___x_630_);
lean_inc(v___x_629_);
v___x_631_ = l_Lean_Syntax_eqWithInfo(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_n_628_);
return v___x_631_;
}
else
{
v_x_624_ = v_n_628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_633_, lean_object* v_ys_634_, lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_633_, v_ys_634_, v_x_635_);
lean_dec_ref(v_ys_634_);
lean_dec_ref(v_xs_633_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Lean_Syntax_eqWithInfo(v_x_638_, v_x_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_642_, lean_object* v_ys_643_, lean_object* v_hsz_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_642_, v_ys_643_, v_x_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_648_, lean_object* v_ys_649_, lean_object* v_hsz_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
uint8_t v_res_653_; lean_object* v_r_654_; 
v_res_653_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_648_, v_ys_649_, v_hsz_650_, v_x_651_, v_x_652_);
lean_dec_ref(v_ys_649_);
lean_dec_ref(v_xs_648_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_655_, lean_object* v_stx1_656_, lean_object* v_stx2_657_){
_start:
{
uint8_t v___x_658_; uint8_t v___x_659_; 
lean_inc(v_stx2_657_);
lean_inc(v_stx1_656_);
v___x_658_ = l_Lean_Syntax_eqWithInfo(v_stx1_656_, v_stx2_657_);
v___x_659_ = 1;
if (v___x_658_ == 0)
{
lean_object* v_map_660_; lean_object* v___x_661_; lean_object* v___f_662_; uint8_t v___y_664_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_map_660_ = lean_ctor_get(v_opts_655_, 0);
v___x_661_ = lean_box(v___x_658_);
v___f_662_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_662_, 0, v___x_661_);
v___x_679_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_660_, v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
v___y_664_ = v___x_658_;
goto v___jp_663_;
}
else
{
lean_object* v_val_681_; 
v_val_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v___x_680_);
if (lean_obj_tag(v_val_681_) == 1)
{
uint8_t v_v_682_; 
v_v_682_ = lean_ctor_get_uint8(v_val_681_, 0);
lean_dec_ref(v_val_681_);
v___y_664_ = v_v_682_;
goto v___jp_663_;
}
else
{
lean_dec(v_val_681_);
v___y_664_ = v___x_658_;
goto v___jp_663_;
}
}
v___jp_663_:
{
if (v___y_664_ == 0)
{
lean_dec_ref(v___f_662_);
lean_dec(v_stx2_657_);
lean_dec(v_stx1_656_);
return v___x_658_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_665_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_Syntax_formatStx(v_stx1_656_, v___x_666_, v___x_659_);
v___x_668_ = l_Std_Format_defWidth;
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = l_Std_Format_pretty(v___x_667_, v___x_668_, v___x_669_, v___x_669_);
v___x_671_ = lean_string_append(v___x_665_, v___x_670_);
lean_dec_ref(v___x_670_);
v___x_672_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
v___x_674_ = l_Lean_Syntax_formatStx(v_stx2_657_, v___x_666_, v___x_659_);
v___x_675_ = l_Std_Format_pretty(v___x_674_, v___x_668_, v___x_669_, v___x_669_);
v___x_676_ = lean_string_append(v___x_673_, v___x_675_);
lean_dec_ref(v___x_675_);
v___x_677_ = lean_dbg_trace(v___x_676_, v___f_662_);
v___x_678_ = lean_unbox(v___x_677_);
lean_dec(v___x_677_);
return v___x_678_;
}
}
}
else
{
lean_dec(v_stx2_657_);
lean_dec(v_stx1_656_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_683_, lean_object* v_stx1_684_, lean_object* v_stx2_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_683_, v_stx1_684_, v_stx2_685_);
lean_dec_ref(v_opts_683_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 2)
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v_x_689_, 1);
lean_inc_ref(v_val_690_);
return v_val_690_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Syntax_getAtomVal(v_x_692_);
lean_dec(v_x_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
if (lean_obj_tag(v_x_694_) == 2)
{
lean_object* v_info_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_info_696_ = lean_ctor_get(v_x_694_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_x_694_, 1);
lean_dec(v_unused_704_);
v___x_698_ = v_x_694_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_info_696_);
lean_dec(v_x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_x_695_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_info_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_x_695_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_dec_ref(v_x_695_);
return v_x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_705_, lean_object* v_hyes_706_, lean_object* v_hno_707_){
_start:
{
if (lean_obj_tag(v_stx_705_) == 1)
{
lean_object* v___x_708_; 
lean_dec(v_hno_707_);
v___x_708_ = lean_apply_1(v_hyes_706_, v_stx_705_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v_hyes_706_);
lean_dec(v_stx_705_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_apply_1(v_hno_707_, v___x_709_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_711_, lean_object* v_stx_712_, lean_object* v_hyes_713_, lean_object* v_hno_714_){
_start:
{
if (lean_obj_tag(v_stx_712_) == 1)
{
lean_object* v___x_715_; 
lean_dec(v_hno_714_);
v___x_715_ = lean_apply_1(v_hyes_713_, v_stx_712_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_hyes_713_);
lean_dec(v_stx_712_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_apply_1(v_hno_714_, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_718_, lean_object* v_kind_719_, lean_object* v_hyes_720_, lean_object* v_hno_721_){
_start:
{
if (lean_obj_tag(v_stx_718_) == 1)
{
lean_object* v_kind_722_; uint8_t v___x_723_; 
v_kind_722_ = lean_ctor_get(v_stx_718_, 1);
v___x_723_ = lean_name_eq(v_kind_722_, v_kind_719_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v_stx_718_);
lean_dec(v_hyes_720_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_apply_1(v_hno_721_, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; 
lean_dec(v_hno_721_);
v___x_726_ = lean_apply_1(v_hyes_720_, v_stx_718_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_hyes_720_);
lean_dec(v_stx_718_);
v___x_727_ = lean_box(0);
v___x_728_ = lean_apply_1(v_hno_721_, v___x_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_729_, lean_object* v_kind_730_, lean_object* v_hyes_731_, lean_object* v_hno_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_729_, v_kind_730_, v_hyes_731_, v_hno_732_);
lean_dec(v_kind_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_734_, lean_object* v_stx_735_, lean_object* v_kind_736_, lean_object* v_hyes_737_, lean_object* v_hno_738_){
_start:
{
if (lean_obj_tag(v_stx_735_) == 1)
{
lean_object* v_kind_739_; uint8_t v___x_740_; 
v_kind_739_ = lean_ctor_get(v_stx_735_, 1);
v___x_740_ = lean_name_eq(v_kind_739_, v_kind_736_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v_stx_735_);
lean_dec(v_hyes_737_);
v___x_741_ = lean_box(0);
v___x_742_ = lean_apply_1(v_hno_738_, v___x_741_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; 
lean_dec(v_hno_738_);
v___x_743_ = lean_apply_1(v_hyes_737_, v_stx_735_);
return v___x_743_;
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec(v_hyes_737_);
lean_dec(v_stx_735_);
v___x_744_ = lean_box(0);
v___x_745_ = lean_apply_1(v_hno_738_, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_746_, lean_object* v_stx_747_, lean_object* v_kind_748_, lean_object* v_hyes_749_, lean_object* v_hno_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_746_, v_stx_747_, v_kind_748_, v_hyes_749_, v_hno_750_);
lean_dec(v_kind_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 1)
{
lean_inc_ref(v_x_761_);
return v_x_761_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Syntax_asNode(v_x_763_);
lean_dec(v_x_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_765_, lean_object* v_i_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = l_Lean_Syntax_getArg(v_stx_765_, v_i_766_);
v___x_768_ = l_Lean_Syntax_getId(v___x_767_);
lean_dec(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_769_, lean_object* v_i_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Syntax_getIdAt(v_stx_769_, v_i_770_);
lean_dec(v_i_770_);
lean_dec(v_stx_769_);
return v_res_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_772_, lean_object* v_x_773_){
_start:
{
switch(lean_obj_tag(v_x_773_))
{
case 3:
{
lean_object* v_val_774_; uint8_t v___x_775_; 
v_val_774_ = lean_ctor_get(v_x_773_, 2);
v___x_775_ = lean_name_eq(v_id_772_, v_val_774_);
return v___x_775_;
}
case 1:
{
lean_object* v_args_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_args_776_ = lean_ctor_get(v_x_773_, 2);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_array_get_size(v_args_776_);
v___x_779_ = lean_nat_dec_lt(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
return v___x_779_;
}
else
{
if (v___x_779_ == 0)
{
return v___x_779_;
}
else
{
size_t v___x_780_; size_t v___x_781_; uint8_t v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_778_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_772_, v_args_776_, v___x_780_, v___x_781_);
return v___x_782_;
}
}
}
default: 
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_784_, lean_object* v_as_785_, size_t v_i_786_, size_t v_stop_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_eq(v_i_786_, v_stop_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_array_uget_borrowed(v_as_785_, v_i_786_);
v___x_790_ = l_Lean_Syntax_hasIdent(v_id_784_, v___x_789_);
if (v___x_790_ == 0)
{
size_t v___x_791_; size_t v___x_792_; 
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_786_, v___x_791_);
v_i_786_ = v___x_792_;
goto _start;
}
else
{
return v___x_790_;
}
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_795_, lean_object* v_as_796_, lean_object* v_i_797_, lean_object* v_stop_798_){
_start:
{
size_t v_i_boxed_799_; size_t v_stop_boxed_800_; uint8_t v_res_801_; lean_object* v_r_802_; 
v_i_boxed_799_ = lean_unbox_usize(v_i_797_);
lean_dec(v_i_797_);
v_stop_boxed_800_ = lean_unbox_usize(v_stop_798_);
lean_dec(v_stop_798_);
v_res_801_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_795_, v_as_796_, v_i_boxed_799_, v_stop_boxed_800_);
lean_dec_ref(v_as_796_);
lean_dec(v_id_795_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_803_, lean_object* v_x_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Lean_Syntax_hasIdent(v_id_803_, v_x_804_);
lean_dec(v_x_804_);
lean_dec(v_id_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_807_, lean_object* v_fn_808_){
_start:
{
if (lean_obj_tag(v_stx_807_) == 1)
{
lean_object* v_info_809_; lean_object* v_kind_810_; lean_object* v_args_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_info_809_ = lean_ctor_get(v_stx_807_, 0);
v_kind_810_ = lean_ctor_get(v_stx_807_, 1);
v_args_811_ = lean_ctor_get(v_stx_807_, 2);
v_isSharedCheck_819_ = !lean_is_exclusive(v_stx_807_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v_stx_807_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_args_811_);
lean_inc(v_kind_810_);
lean_inc(v_info_809_);
lean_dec(v_stx_807_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_apply_1(v_fn_808_, v_args_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 2, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_info_809_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_kind_810_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_dec_ref(v_fn_808_);
return v_stx_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_820_, lean_object* v_i_821_, lean_object* v_fn_822_){
_start:
{
if (lean_obj_tag(v_stx_820_) == 1)
{
lean_object* v_info_823_; lean_object* v_kind_824_; lean_object* v_args_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_info_823_ = lean_ctor_get(v_stx_820_, 0);
v_kind_824_ = lean_ctor_get(v_stx_820_, 1);
v_args_825_ = lean_ctor_get(v_stx_820_, 2);
v___x_826_ = lean_array_get_size(v_args_825_);
v___x_827_ = lean_nat_dec_lt(v_i_821_, v___x_826_);
if (v___x_827_ == 0)
{
lean_dec_ref(v_fn_822_);
return v_stx_820_;
}
else
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_839_; 
lean_inc_ref(v_args_825_);
lean_inc(v_kind_824_);
lean_inc(v_info_823_);
v_isSharedCheck_839_ = !lean_is_exclusive(v_stx_820_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_840_ = lean_ctor_get(v_stx_820_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_stx_820_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_stx_820_, 0);
lean_dec(v_unused_842_);
v___x_829_ = v_stx_820_;
v_isShared_830_ = v_isSharedCheck_839_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_stx_820_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_839_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_v_831_; lean_object* v___x_832_; lean_object* v_xs_x27_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v_v_831_ = lean_array_fget(v_args_825_, v_i_821_);
v___x_832_ = lean_box(0);
v_xs_x27_833_ = lean_array_fset(v_args_825_, v_i_821_, v___x_832_);
v___x_834_ = lean_apply_1(v_fn_822_, v_v_831_);
v___x_835_ = lean_array_fset(v_xs_x27_833_, v_i_821_, v___x_834_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 2, v___x_835_);
v___x_837_ = v___x_829_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_info_823_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_kind_824_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_dec_ref(v_fn_822_);
return v_stx_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_843_, lean_object* v_i_844_, lean_object* v_fn_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Syntax_modifyArg(v_stx_843_, v_i_844_, v_fn_845_);
lean_dec(v_i_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_847_, lean_object* v_kind_848_, lean_object* v_toPure_849_, lean_object* v_____do__lift_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_851_, 0, v_info_847_);
lean_ctor_set(v___x_851_, 1, v_kind_848_);
lean_ctor_set(v___x_851_, 2, v_____do__lift_850_);
v___x_852_ = lean_apply_2(v_toPure_849_, lean_box(0), v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_853_, lean_object* v_x_854_, lean_object* v_o_855_){
_start:
{
if (lean_obj_tag(v_o_855_) == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_apply_2(v_toPure_853_, lean_box(0), v_x_854_);
return v___x_856_;
}
else
{
lean_object* v_val_857_; lean_object* v___x_858_; 
lean_dec(v_x_854_);
v_val_857_ = lean_ctor_get(v_o_855_, 0);
lean_inc(v_val_857_);
lean_dec_ref(v_o_855_);
v___x_858_ = lean_apply_2(v_toPure_853_, lean_box(0), v_val_857_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_859_, lean_object* v_fn_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 1)
{
lean_object* v_toApplicative_862_; lean_object* v_toBind_863_; lean_object* v_toPure_864_; lean_object* v_info_865_; lean_object* v_kind_866_; lean_object* v_args_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_toApplicative_862_ = lean_ctor_get(v_inst_859_, 0);
v_toBind_863_ = lean_ctor_get(v_inst_859_, 1);
lean_inc_n(v_toBind_863_, 2);
v_toPure_864_ = lean_ctor_get(v_toApplicative_862_, 1);
lean_inc_n(v_toPure_864_, 2);
v_info_865_ = lean_ctor_get(v_x_861_, 0);
v_kind_866_ = lean_ctor_get(v_x_861_, 1);
v_args_867_ = lean_ctor_get(v_x_861_, 2);
lean_inc(v_kind_866_);
lean_inc(v_info_865_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_868_, 0, v_info_865_);
lean_closure_set(v___f_868_, 1, v_kind_866_);
lean_closure_set(v___f_868_, 2, v_toPure_864_);
lean_inc_ref(v_args_867_);
lean_inc(v_fn_860_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_869_, 0, v_inst_859_);
lean_closure_set(v___f_869_, 1, v_fn_860_);
lean_closure_set(v___f_869_, 2, v_args_867_);
lean_closure_set(v___f_869_, 3, v_toBind_863_);
lean_closure_set(v___f_869_, 4, v___f_868_);
lean_closure_set(v___f_869_, 5, v_toPure_864_);
v___x_870_ = lean_apply_1(v_fn_860_, v_x_861_);
v___x_871_ = lean_apply_4(v_toBind_863_, lean_box(0), lean_box(0), v___x_870_, v___f_869_);
return v___x_871_;
}
else
{
lean_object* v_toApplicative_872_; lean_object* v_toBind_873_; lean_object* v_toPure_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_toApplicative_872_ = lean_ctor_get(v_inst_859_, 0);
lean_inc_ref(v_toApplicative_872_);
v_toBind_873_ = lean_ctor_get(v_inst_859_, 1);
lean_inc(v_toBind_873_);
lean_dec_ref(v_inst_859_);
v_toPure_874_ = lean_ctor_get(v_toApplicative_872_, 1);
lean_inc(v_toPure_874_);
lean_dec_ref(v_toApplicative_872_);
lean_inc(v_x_861_);
v___f_875_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_875_, 0, v_toPure_874_);
lean_closure_set(v___f_875_, 1, v_x_861_);
v___x_876_ = lean_apply_1(v_fn_860_, v_x_861_);
v___x_877_ = lean_apply_4(v_toBind_873_, lean_box(0), lean_box(0), v___x_876_, v___f_875_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_878_, lean_object* v_fn_879_, lean_object* v_args_880_, lean_object* v_toBind_881_, lean_object* v___f_882_, lean_object* v_toPure_883_, lean_object* v_____do__lift_884_){
_start:
{
if (lean_obj_tag(v_____do__lift_884_) == 0)
{
lean_object* v___x_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_toPure_883_);
lean_inc_ref(v_inst_878_);
v___x_885_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_885_, 0, v_inst_878_);
lean_closure_set(v___x_885_, 1, v_fn_879_);
v_sz_886_ = lean_array_size(v_args_880_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_878_, v___x_885_, v_sz_886_, v___x_887_, v_args_880_);
v___x_889_ = lean_apply_4(v_toBind_881_, lean_box(0), lean_box(0), v___x_888_, v___f_882_);
return v___x_889_;
}
else
{
lean_object* v_val_890_; lean_object* v___x_891_; 
lean_dec(v___f_882_);
lean_dec(v_toBind_881_);
lean_dec_ref(v_args_880_);
lean_dec(v_fn_879_);
lean_dec_ref(v_inst_878_);
v_val_890_ = lean_ctor_get(v_____do__lift_884_, 0);
lean_inc(v_val_890_);
lean_dec_ref(v_____do__lift_884_);
v___x_891_ = lean_apply_2(v_toPure_883_, lean_box(0), v_val_890_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_892_, lean_object* v_inst_893_, lean_object* v_fn_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Syntax_replaceM___redArg(v_inst_893_, v_fn_894_, v_x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_897_, lean_object* v_kind_898_, lean_object* v_fn_899_, lean_object* v_args_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_901_, 0, v_info_897_);
lean_ctor_set(v___x_901_, 1, v_kind_898_);
lean_ctor_set(v___x_901_, 2, v_args_900_);
v___x_902_ = lean_apply_1(v_fn_899_, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_903_, lean_object* v_fn_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 1)
{
lean_object* v_toBind_906_; lean_object* v_info_907_; lean_object* v_kind_908_; lean_object* v_args_909_; lean_object* v___f_910_; lean_object* v___x_911_; size_t v_sz_912_; size_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_toBind_906_ = lean_ctor_get(v_inst_903_, 1);
lean_inc(v_toBind_906_);
v_info_907_ = lean_ctor_get(v_x_905_, 0);
lean_inc(v_info_907_);
v_kind_908_ = lean_ctor_get(v_x_905_, 1);
lean_inc(v_kind_908_);
v_args_909_ = lean_ctor_get(v_x_905_, 2);
lean_inc_ref(v_args_909_);
lean_dec_ref(v_x_905_);
lean_inc(v_fn_904_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_910_, 0, v_info_907_);
lean_closure_set(v___f_910_, 1, v_kind_908_);
lean_closure_set(v___f_910_, 2, v_fn_904_);
lean_inc_ref(v_inst_903_);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_911_, 0, v_inst_903_);
lean_closure_set(v___x_911_, 1, v_fn_904_);
v_sz_912_ = lean_array_size(v_args_909_);
v___x_913_ = ((size_t)0ULL);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_903_, v___x_911_, v_sz_912_, v___x_913_, v_args_909_);
v___x_915_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_914_, v___f_910_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; 
lean_dec_ref(v_inst_903_);
v___x_916_ = lean_apply_1(v_fn_904_, v_x_905_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_917_, lean_object* v_inst_918_, lean_object* v_fn_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_918_, v_fn_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_922_, lean_object* v_x_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_apply_1(v_fn_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_944_, lean_object* v_stx_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_946_, 0, v_fn_944_);
v___x_947_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_948_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_947_, v___f_946_, v_stx_945_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_949_) == 0)
{
lean_object* v_leading_952_; lean_object* v_trailing_953_; lean_object* v_pos_954_; lean_object* v_endPos_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_982_; 
v_leading_952_ = lean_ctor_get(v_x_949_, 0);
v_trailing_953_ = lean_ctor_get(v_x_949_, 2);
v_pos_954_ = lean_ctor_get(v_x_949_, 1);
v_endPos_955_ = lean_ctor_get(v_x_949_, 3);
v_isSharedCheck_982_ = !lean_is_exclusive(v_x_949_);
if (v_isSharedCheck_982_ == 0)
{
v___x_957_ = v_x_949_;
v_isShared_958_ = v_isSharedCheck_982_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_endPos_955_);
lean_inc(v_trailing_953_);
lean_inc(v_pos_954_);
lean_inc(v_leading_952_);
lean_dec(v_x_949_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_982_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_str_959_; lean_object* v_stopPos_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_980_; 
v_str_959_ = lean_ctor_get(v_leading_952_, 0);
v_stopPos_960_ = lean_ctor_get(v_leading_952_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v_leading_952_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v_leading_952_, 1);
lean_dec(v_unused_981_);
v___x_962_ = v_leading_952_;
v_isShared_963_ = v_isSharedCheck_980_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_stopPos_960_);
lean_inc(v_str_959_);
lean_dec(v_leading_952_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_980_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_str_964_; lean_object* v_startPos_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_978_; 
v_str_964_ = lean_ctor_get(v_trailing_953_, 0);
v_startPos_965_ = lean_ctor_get(v_trailing_953_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_trailing_953_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_trailing_953_, 2);
lean_dec(v_unused_979_);
v___x_967_ = v_trailing_953_;
v_isShared_968_ = v_isSharedCheck_978_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_startPos_965_);
lean_inc(v_str_964_);
lean_dec(v_trailing_953_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_978_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 2, v_stopPos_960_);
lean_ctor_set(v___x_967_, 1, v_x_950_);
lean_ctor_set(v___x_967_, 0, v_str_959_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_str_959_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_x_950_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_stopPos_960_);
v___x_970_ = v_reuseFailAlloc_977_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v_x_951_);
lean_ctor_set(v___x_962_, 1, v_startPos_965_);
lean_ctor_set(v___x_962_, 0, v_str_964_);
v___x_972_ = v___x_962_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_str_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_startPos_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_x_951_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 2, v___x_972_);
lean_ctor_set(v___x_957_, 0, v___x_970_);
v___x_974_ = v___x_957_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_pos_954_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_endPos_955_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_951_);
lean_dec(v_x_950_);
return v_x_949_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v_a_986_, lean_object* v_b_987_){
_start:
{
lean_object* v_startInclusive_988_; lean_object* v_endExclusive_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_startInclusive_988_ = lean_ctor_get(v___x_983_, 1);
v_endExclusive_989_ = lean_ctor_get(v___x_983_, 2);
v___x_990_ = lean_nat_sub(v_endExclusive_989_, v_startInclusive_988_);
v___x_991_ = lean_nat_dec_eq(v_a_986_, v___x_990_);
lean_dec(v___x_990_);
if (v___x_991_ == 0)
{
uint32_t v___x_992_; lean_object* v___x_993_; uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_992_ = 10;
v___x_993_ = lean_nat_add(v___x_984_, v_a_986_);
v___x_994_ = lean_string_utf8_get_fast(v___x_985_, v___x_993_);
v___x_995_ = lean_uint32_dec_eq(v___x_994_, v___x_992_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v_a_986_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_string_utf8_next_fast(v___x_985_, v___x_993_);
lean_dec(v___x_993_);
v___x_998_ = lean_nat_sub(v___x_997_, v___x_984_);
v_a_986_ = v___x_998_;
v_b_987_ = v___x_996_;
goto _start;
}
else
{
lean_object* v___x_1000_; 
lean_dec(v___x_993_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_a_986_);
return v___x_1000_;
}
}
else
{
lean_dec(v_a_986_);
lean_inc(v_b_987_);
return v_b_987_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_1001_, lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1001_, v___x_1002_, v___x_1003_, v_a_1004_, v_b_1005_);
lean_dec(v_b_1005_);
lean_dec_ref(v___x_1003_);
lean_dec(v___x_1002_);
lean_dec_ref(v___x_1001_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_1007_){
_start:
{
lean_object* v_str_1008_; lean_object* v_startPos_1009_; lean_object* v_stopPos_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1030_; 
v_str_1008_ = lean_ctor_get(v_trail_1007_, 0);
v_startPos_1009_ = lean_ctor_get(v_trail_1007_, 1);
v_stopPos_1010_ = lean_ctor_get(v_trail_1007_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_trail_1007_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1012_ = v_trail_1007_;
v_isShared_1013_ = v_isSharedCheck_1030_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_stopPos_1010_);
lean_inc(v_startPos_1009_);
lean_inc(v_str_1008_);
lean_dec(v_trail_1007_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1030_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_string_is_valid_pos(v_str_1008_, v_startPos_1009_);
if (v___x_1017_ == 0)
{
lean_del_object(v___x_1012_);
lean_dec_ref(v_str_1008_);
goto v___jp_1014_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_string_is_valid_pos(v_str_1008_, v_stopPos_1010_);
if (v___x_1018_ == 0)
{
lean_del_object(v___x_1012_);
lean_dec_ref(v_str_1008_);
goto v___jp_1014_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_le(v_startPos_1009_, v_stopPos_1010_);
if (v___x_1019_ == 0)
{
lean_del_object(v___x_1012_);
lean_dec_ref(v_str_1008_);
goto v___jp_1014_;
}
else
{
lean_object* v___x_1021_; 
lean_inc(v_stopPos_1010_);
lean_inc(v_startPos_1009_);
lean_inc_ref(v_str_1008_);
if (v_isShared_1013_ == 0)
{
v___x_1021_ = v___x_1012_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_str_1008_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_startPos_1009_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_stopPos_1010_);
v___x_1021_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v_searcher_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_searcher_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_box(0);
v___x_1024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1021_, v_startPos_1009_, v_str_1008_, v_searcher_1022_, v___x_1023_);
lean_dec_ref(v_str_1008_);
lean_dec_ref(v___x_1021_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_nat_sub(v_stopPos_1010_, v_startPos_1009_);
lean_dec(v_stopPos_1010_);
v___x_1026_ = lean_nat_add(v_startPos_1009_, v___x_1025_);
lean_dec(v___x_1025_);
lean_dec(v_startPos_1009_);
return v___x_1026_;
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1028_; 
lean_dec(v_stopPos_1010_);
v_val_1027_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_val_1027_);
lean_dec_ref(v___x_1024_);
v___x_1028_ = lean_nat_add(v_startPos_1009_, v_val_1027_);
lean_dec(v_val_1027_);
lean_dec(v_startPos_1009_);
return v___x_1028_;
}
}
}
}
}
v___jp_1014_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_nat_sub(v_stopPos_1010_, v_startPos_1009_);
lean_dec(v_stopPos_1010_);
v___x_1016_ = lean_nat_add(v_startPos_1009_, v___x_1015_);
lean_dec(v___x_1015_);
lean_dec(v_startPos_1009_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_inst_1034_, lean_object* v_R_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_, lean_object* v_c_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1031_, v___x_1032_, v___x_1033_, v_a_1036_, v_b_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v_inst_1043_, lean_object* v_R_1044_, lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v_c_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1040_, v___x_1041_, v___x_1042_, v_inst_1043_, v_R_1044_, v_a_1045_, v_b_1046_, v_c_1047_);
lean_dec(v_b_1046_);
lean_dec_ref(v___x_1042_);
lean_dec(v___x_1041_);
lean_dec_ref(v___x_1040_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___y_1052_; 
switch(lean_obj_tag(v_x_1049_))
{
case 2:
{
lean_object* v_info_1055_; 
v_info_1055_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_info_1055_);
if (lean_obj_tag(v_info_1055_) == 0)
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1068_; 
v_val_1056_ = lean_ctor_get(v_x_1049_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1049_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_x_1049_, 0);
lean_dec(v_unused_1069_);
v___x_1058_ = v_x_1049_;
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v_x_1049_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_trailing_1060_; lean_object* v_trailStop_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v_trailing_1060_ = lean_ctor_get(v_info_1055_, 2);
lean_inc_ref(v_trailing_1060_);
v_trailStop_1061_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1060_);
lean_inc(v_trailStop_1061_);
v___x_1062_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1055_, v_a_1050_, v_trailStop_1061_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1062_);
v___x_1064_ = v___x_1058_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_val_1056_);
v___x_1064_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_trailStop_1061_);
return v___x_1066_;
}
}
}
else
{
lean_dec(v_info_1055_);
lean_dec_ref(v_x_1049_);
v___y_1052_ = v_a_1050_;
goto v___jp_1051_;
}
}
case 3:
{
lean_object* v_info_1070_; 
v_info_1070_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_info_1070_);
if (lean_obj_tag(v_info_1070_) == 0)
{
lean_object* v_rawVal_1071_; lean_object* v_val_1072_; lean_object* v_preresolved_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1085_; 
v_rawVal_1071_ = lean_ctor_get(v_x_1049_, 1);
v_val_1072_ = lean_ctor_get(v_x_1049_, 2);
v_preresolved_1073_ = lean_ctor_get(v_x_1049_, 3);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1049_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_x_1049_, 0);
lean_dec(v_unused_1086_);
v___x_1075_ = v_x_1049_;
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_preresolved_1073_);
lean_inc(v_val_1072_);
lean_inc(v_rawVal_1071_);
lean_dec(v_x_1049_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_trailing_1077_; lean_object* v_trailStop_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_trailing_1077_ = lean_ctor_get(v_info_1070_, 2);
lean_inc_ref(v_trailing_1077_);
v_trailStop_1078_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1077_);
lean_inc(v_trailStop_1078_);
v___x_1079_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1070_, v_a_1050_, v_trailStop_1078_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1079_);
v___x_1081_ = v___x_1075_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_rawVal_1071_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_val_1072_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_preresolved_1073_);
v___x_1081_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_trailStop_1078_);
return v___x_1083_;
}
}
}
else
{
lean_dec_ref(v_x_1049_);
lean_dec(v_info_1070_);
v___y_1052_ = v_a_1050_;
goto v___jp_1051_;
}
}
default: 
{
lean_dec(v_x_1049_);
v___y_1052_ = v_a_1050_;
goto v___jp_1051_;
}
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___y_1052_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
switch(lean_obj_tag(v___y_1087_))
{
case 2:
{
lean_object* v_info_1092_; 
v_info_1092_ = lean_ctor_get(v___y_1087_, 0);
lean_inc(v_info_1092_);
if (lean_obj_tag(v_info_1092_) == 0)
{
lean_object* v_val_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1105_; 
v_val_1093_ = lean_ctor_get(v___y_1087_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___y_1087_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v___y_1087_, 0);
lean_dec(v_unused_1106_);
v___x_1095_ = v___y_1087_;
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_val_1093_);
lean_dec(v___y_1087_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_trailing_1097_; lean_object* v_trailStop_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v_trailing_1097_ = lean_ctor_get(v_info_1092_, 2);
lean_inc_ref(v_trailing_1097_);
v_trailStop_1098_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1097_);
lean_inc(v_trailStop_1098_);
v___x_1099_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1092_, v___y_1088_, v_trailStop_1098_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1099_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_val_1093_);
v___x_1101_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_trailStop_1098_);
return v___x_1103_;
}
}
}
else
{
lean_dec(v_info_1092_);
lean_dec_ref(v___y_1087_);
goto v___jp_1089_;
}
}
case 3:
{
lean_object* v_info_1107_; 
v_info_1107_ = lean_ctor_get(v___y_1087_, 0);
lean_inc(v_info_1107_);
if (lean_obj_tag(v_info_1107_) == 0)
{
lean_object* v_rawVal_1108_; lean_object* v_val_1109_; lean_object* v_preresolved_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1122_; 
v_rawVal_1108_ = lean_ctor_get(v___y_1087_, 1);
v_val_1109_ = lean_ctor_get(v___y_1087_, 2);
v_preresolved_1110_ = lean_ctor_get(v___y_1087_, 3);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___y_1087_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___y_1087_, 0);
lean_dec(v_unused_1123_);
v___x_1112_ = v___y_1087_;
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_preresolved_1110_);
lean_inc(v_val_1109_);
lean_inc(v_rawVal_1108_);
lean_dec(v___y_1087_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_trailing_1114_; lean_object* v_trailStop_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v_trailing_1114_ = lean_ctor_get(v_info_1107_, 2);
lean_inc_ref(v_trailing_1114_);
v_trailStop_1115_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1114_);
lean_inc(v_trailStop_1115_);
v___x_1116_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1107_, v___y_1088_, v_trailStop_1115_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1116_);
v___x_1118_ = v___x_1112_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_rawVal_1108_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_val_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_preresolved_1110_);
v___x_1118_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_trailStop_1115_);
return v___x_1120_;
}
}
}
else
{
lean_dec(v_info_1107_);
lean_dec_ref(v___y_1087_);
goto v___jp_1089_;
}
}
default: 
{
lean_dec(v___y_1087_);
goto v___jp_1089_;
}
}
v___jp_1089_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___y_1088_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1124_, lean_object* v___y_1125_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 1)
{
lean_object* v_info_1126_; lean_object* v_kind_1127_; lean_object* v_args_1128_; lean_object* v___x_1129_; lean_object* v_fst_1130_; 
v_info_1126_ = lean_ctor_get(v_x_1124_, 0);
lean_inc(v_info_1126_);
v_kind_1127_ = lean_ctor_get(v_x_1124_, 1);
lean_inc(v_kind_1127_);
v_args_1128_ = lean_ctor_get(v_x_1124_, 2);
lean_inc_ref(v_args_1128_);
v___x_1129_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1124_, v___y_1125_);
v_fst_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_fst_1130_);
if (lean_obj_tag(v_fst_1130_) == 0)
{
lean_object* v_snd_1131_; size_t v_sz_1132_; size_t v___x_1133_; lean_object* v___x_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_snd_1131_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_snd_1131_);
lean_dec_ref(v___x_1129_);
v_sz_1132_ = lean_array_size(v_args_1128_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1132_, v___x_1133_, v_args_1128_, v_snd_1131_);
v_fst_1135_ = lean_ctor_get(v___x_1134_, 0);
v_snd_1136_ = lean_ctor_get(v___x_1134_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v___x_1134_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v___x_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1140_, 0, v_info_1126_);
lean_ctor_set(v___x_1140_, 1, v_kind_1127_);
lean_ctor_set(v___x_1140_, 2, v_fst_1135_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_snd_1136_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_args_1128_);
lean_dec(v_kind_1127_);
lean_dec(v_info_1126_);
v_snd_1145_ = lean_ctor_get(v___x_1129_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1129_, 0);
lean_dec(v_unused_1154_);
v___x_1147_ = v___x_1129_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_dec(v___x_1129_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_val_1149_; lean_object* v___x_1151_; 
v_val_1149_ = lean_ctor_get(v_fst_1130_, 0);
lean_inc(v_val_1149_);
lean_dec_ref(v_fst_1130_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v_val_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_val_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_snd_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v_fst_1156_; 
lean_inc(v_x_1124_);
v___x_1155_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1124_, v___y_1125_);
v_fst_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_fst_1156_);
if (lean_obj_tag(v_fst_1156_) == 0)
{
lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_snd_1157_ = lean_ctor_get(v___x_1155_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v___x_1155_, 0);
lean_dec(v_unused_1165_);
v___x_1159_ = v___x_1155_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v___x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_x_1124_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_x_1124_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_snd_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_snd_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_x_1124_);
v_snd_1166_ = lean_ctor_get(v___x_1155_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v___x_1155_, 0);
lean_dec(v_unused_1175_);
v___x_1168_ = v___x_1155_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1166_);
lean_dec(v___x_1155_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_val_1170_; lean_object* v___x_1172_; 
v_val_1170_ = lean_ctor_get(v_fst_1156_, 0);
lean_inc(v_val_1170_);
lean_dec_ref(v_fst_1156_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_val_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_val_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_snd_1166_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1176_, size_t v_i_1177_, lean_object* v_bs_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_usize_dec_lt(v_i_1177_, v_sz_1176_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_bs_1178_);
lean_ctor_set(v___x_1181_, 1, v___y_1179_);
return v___x_1181_;
}
else
{
lean_object* v_v_1182_; lean_object* v___x_1183_; lean_object* v_fst_1184_; lean_object* v_snd_1185_; lean_object* v___x_1186_; lean_object* v_bs_x27_1187_; size_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v_v_1182_ = lean_array_uget_borrowed(v_bs_1178_, v_i_1177_);
lean_inc(v_v_1182_);
v___x_1183_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1182_, v___y_1179_);
v_fst_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_fst_1184_);
v_snd_1185_ = lean_ctor_get(v___x_1183_, 1);
lean_inc(v_snd_1185_);
lean_dec_ref(v___x_1183_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v_bs_x27_1187_ = lean_array_uset(v_bs_1178_, v_i_1177_, v___x_1186_);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_add(v_i_1177_, v___x_1188_);
v___x_1190_ = lean_array_uset(v_bs_x27_1187_, v_i_1177_, v_fst_1184_);
v_i_1177_ = v___x_1189_;
v_bs_1178_ = v___x_1190_;
v___y_1179_ = v_snd_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_bs_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1196_, v_i_boxed_1197_, v_bs_1194_, v___y_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_fst_1202_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1199_, v___x_1200_);
v_fst_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_fst_1202_);
lean_dec_ref(v___x_1201_);
return v_fst_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1203_, lean_object* v_x_1204_){
_start:
{
switch(lean_obj_tag(v_x_1204_))
{
case 2:
{
lean_object* v_info_1205_; lean_object* v_val_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_info_1205_ = lean_ctor_get(v_x_1204_, 0);
v_val_1206_ = lean_ctor_get(v_x_1204_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v_x_1204_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_val_1206_);
lean_inc(v_info_1205_);
lean_dec(v_x_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1203_, v_info_1205_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_val_1206_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
case 3:
{
lean_object* v_info_1215_; lean_object* v_rawVal_1216_; lean_object* v_val_1217_; lean_object* v_preresolved_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_info_1215_ = lean_ctor_get(v_x_1204_, 0);
v_rawVal_1216_ = lean_ctor_get(v_x_1204_, 1);
v_val_1217_ = lean_ctor_get(v_x_1204_, 2);
v_preresolved_1218_ = lean_ctor_get(v_x_1204_, 3);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v_x_1204_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_preresolved_1218_);
lean_inc(v_val_1217_);
lean_inc(v_rawVal_1216_);
lean_inc(v_info_1215_);
lean_dec(v_x_1204_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1203_, v_info_1215_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_rawVal_1216_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_val_1217_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_preresolved_1218_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
case 1:
{
lean_object* v_info_1227_; lean_object* v_kind_1228_; lean_object* v_args_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_info_1227_ = lean_ctor_get(v_x_1204_, 0);
v_kind_1228_ = lean_ctor_get(v_x_1204_, 1);
v_args_1229_ = lean_ctor_get(v_x_1204_, 2);
v___x_1230_ = lean_array_get_size(v_args_1229_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_nat_dec_eq(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1244_; 
lean_inc_ref(v_args_1229_);
lean_inc(v_kind_1228_);
lean_inc(v_info_1227_);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; lean_object* v_unused_1246_; lean_object* v_unused_1247_; 
v_unused_1245_ = lean_ctor_get(v_x_1204_, 2);
lean_dec(v_unused_1245_);
v_unused_1246_ = lean_ctor_get(v_x_1204_, 1);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v_x_1204_, 0);
lean_dec(v_unused_1247_);
v___x_1234_ = v_x_1204_;
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v_x_1204_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v_i_1237_; lean_object* v___x_1238_; lean_object* v_last_1239_; lean_object* v_args_1240_; lean_object* v___x_1242_; 
v___x_1236_ = lean_unsigned_to_nat(1u);
v_i_1237_ = lean_nat_sub(v___x_1230_, v___x_1236_);
v___x_1238_ = lean_array_fget_borrowed(v_args_1229_, v_i_1237_);
lean_inc(v___x_1238_);
v_last_1239_ = l_Lean_Syntax_updateTrailing(v_trailing_1203_, v___x_1238_);
v_args_1240_ = lean_array_fset(v_args_1229_, v_i_1237_, v_last_1239_);
lean_dec(v_i_1237_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 2, v_args_1240_);
v___x_1242_ = v___x_1234_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_info_1227_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_kind_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_args_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_dec_ref(v_trailing_1203_);
return v_x_1204_;
}
}
default: 
{
lean_dec_ref(v_trailing_1203_);
return v_x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
return v_x_1248_;
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; lean_object* v___x_1252_; 
v_head_1250_ = lean_ctor_get(v_x_1249_, 0);
lean_inc(v_head_1250_);
v_tail_1251_ = lean_ctor_get(v_x_1249_, 1);
lean_inc(v_tail_1251_);
lean_dec_ref(v_x_1249_);
v___x_1252_ = l_Lean_Name_append(v_x_1248_, v_head_1250_);
v_x_1248_ = v___x_1252_;
v_x_1249_ = v_tail_1251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1256_, lean_object* v_nFields_x3f_1257_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1257_) == 1)
{
lean_object* v_val_1258_; lean_object* v_nameComps_1259_; lean_object* v___x_1260_; lean_object* v_nPrefix_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_namePrefix_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_val_1258_ = lean_ctor_get(v_nFields_x3f_1257_, 0);
v_nameComps_1259_ = l_Lean_Name_components(v_n_1256_);
v___x_1260_ = l_List_lengthTR___redArg(v_nameComps_1259_);
v_nPrefix_1261_ = lean_nat_sub(v___x_1260_, v_val_1258_);
lean_dec(v___x_1260_);
v___x_1262_ = lean_box(0);
v___x_1263_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0));
lean_inc(v_nPrefix_1261_);
lean_inc(v_nameComps_1259_);
v___x_1264_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1259_, v_nameComps_1259_, v_nPrefix_1261_, v___x_1263_);
v_namePrefix_1265_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(v___x_1262_, v___x_1264_);
v___x_1266_ = l_List_drop___redArg(v_nPrefix_1261_, v_nameComps_1259_);
lean_dec(v_nameComps_1259_);
v___x_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_namePrefix_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Name_components(v_n_1256_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1269_, lean_object* v_nFields_x3f_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1269_, v_nFields_x3f_1270_);
lean_dec(v_nFields_x3f_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__3(lean_object* v_msg_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_panic_fn_borrowed(v___x_1273_, v_msg_1272_);
return v___x_1274_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1276_ = lean_string_utf8_byte_size(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___x_1278_);
lean_ctor_set(v___x_1280_, 2, v___x_1277_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_rawVal_1281_, lean_object* v_pos_1282_, lean_object* v_trailing_1283_, lean_object* v_leading_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
if (lean_obj_tag(v_a_1285_) == 0)
{
lean_object* v___x_1287_; 
lean_dec_ref(v_leading_1284_);
lean_dec_ref(v_trailing_1283_);
v___x_1287_ = l_List_reverse___redArg(v_a_1286_);
return v___x_1287_;
}
else
{
lean_object* v_head_1288_; lean_object* v_snd_1289_; lean_object* v_tail_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1320_; 
v_head_1288_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_head_1288_);
v_snd_1289_ = lean_ctor_get(v_head_1288_, 1);
lean_inc(v_snd_1289_);
v_tail_1290_ = lean_ctor_get(v_a_1285_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1285_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v_a_1285_, 0);
lean_dec(v_unused_1321_);
v___x_1292_ = v_a_1285_;
v_isShared_1293_ = v_isSharedCheck_1320_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_tail_1290_);
lean_dec(v_a_1285_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1320_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fst_1294_; lean_object* v_startPos_1295_; lean_object* v_stopPos_1296_; lean_object* v_startPos_1297_; lean_object* v_stopPos_1298_; lean_object* v_off_1299_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1314_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_fst_1294_ = lean_ctor_get(v_head_1288_, 0);
lean_inc(v_fst_1294_);
lean_dec(v_head_1288_);
v_startPos_1295_ = lean_ctor_get(v_snd_1289_, 1);
v_stopPos_1296_ = lean_ctor_get(v_snd_1289_, 2);
v_startPos_1297_ = lean_ctor_get(v_rawVal_1281_, 1);
v_stopPos_1298_ = lean_ctor_get(v_rawVal_1281_, 2);
v_off_1299_ = lean_nat_sub(v_startPos_1295_, v_startPos_1297_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_nat_dec_eq(v_off_1299_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1);
v___y_1314_ = v___x_1319_;
goto v___jp_1313_;
}
else
{
lean_inc_ref(v_leading_1284_);
v___y_1314_ = v_leading_1284_;
goto v___jp_1313_;
}
v___jp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_info_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1303_ = lean_nat_add(v_off_1299_, v_pos_1282_);
lean_dec(v_off_1299_);
v___x_1304_ = lean_nat_sub(v_stopPos_1296_, v_startPos_1295_);
v___x_1305_ = lean_nat_add(v___x_1304_, v___x_1303_);
lean_dec(v___x_1304_);
v_info_1306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1306_, 0, v___y_1301_);
lean_ctor_set(v_info_1306_, 1, v___x_1303_);
lean_ctor_set(v_info_1306_, 2, v___y_1302_);
lean_ctor_set(v_info_1306_, 3, v___x_1305_);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1308_, 0, v_info_1306_);
lean_ctor_set(v___x_1308_, 1, v_snd_1289_);
lean_ctor_set(v___x_1308_, 2, v_fst_1294_);
lean_ctor_set(v___x_1308_, 3, v___x_1307_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v_a_1286_);
lean_ctor_set(v___x_1292_, 0, v___x_1308_);
v___x_1310_ = v___x_1292_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_a_1286_);
v___x_1310_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v_a_1285_ = v_tail_1290_;
v_a_1286_ = v___x_1310_;
goto _start;
}
}
v___jp_1313_:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_eq(v_stopPos_1296_, v_stopPos_1298_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1);
v___y_1301_ = v___y_1314_;
v___y_1302_ = v___x_1316_;
goto v___jp_1300_;
}
else
{
lean_inc_ref(v_trailing_1283_);
v___y_1301_ = v___y_1314_;
v___y_1302_ = v_trailing_1283_;
goto v___jp_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___boxed(lean_object* v_rawVal_1322_, lean_object* v_pos_1323_, lean_object* v_trailing_1324_, lean_object* v_leading_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(v_rawVal_1322_, v_pos_1323_, v_trailing_1324_, v_leading_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_pos_1323_);
lean_dec_ref(v_rawVal_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 0)
{
return v_x_1329_;
}
else
{
lean_object* v_head_1331_; lean_object* v_tail_1332_; lean_object* v_startPos_1333_; lean_object* v_stopPos_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_head_1331_ = lean_ctor_get(v_x_1330_, 0);
v_tail_1332_ = lean_ctor_get(v_x_1330_, 1);
v_startPos_1333_ = lean_ctor_get(v_head_1331_, 1);
v_stopPos_1334_ = lean_ctor_get(v_head_1331_, 2);
v___x_1335_ = lean_nat_sub(v_stopPos_1334_, v_startPos_1333_);
v___x_1336_ = lean_nat_add(v_x_1329_, v___x_1335_);
lean_dec(v___x_1335_);
lean_dec(v_x_1329_);
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_add(v___x_1336_, v___x_1337_);
lean_dec(v___x_1336_);
v_x_1329_ = v___x_1338_;
v_x_1330_ = v_tail_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_spec__2___boxed(lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(v_x_1340_, v_x_1341_);
lean_dec(v_x_1341_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
if (lean_obj_tag(v_a_1344_) == 0)
{
lean_object* v___x_1346_; 
lean_dec(v_info_1343_);
v___x_1346_ = l_List_reverse___redArg(v_a_1345_);
return v___x_1346_;
}
else
{
lean_object* v_head_1347_; lean_object* v_tail_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1363_; 
v_head_1347_ = lean_ctor_get(v_a_1344_, 0);
v_tail_1348_ = lean_ctor_get(v_a_1344_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_a_1344_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1350_ = v_a_1344_;
v_isShared_1351_ = v_isSharedCheck_1363_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_tail_1348_);
lean_inc(v_head_1347_);
lean_dec(v_a_1344_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1363_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1352_ = 1;
lean_inc(v_head_1347_);
v___x_1353_ = l_Lean_Name_toString(v_head_1347_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_string_utf8_byte_size(v___x_1353_);
v___x_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1354_);
lean_ctor_set(v___x_1356_, 2, v___x_1355_);
v___x_1357_ = lean_box(0);
lean_inc(v_info_1343_);
v___x_1358_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1358_, 0, v_info_1343_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v_head_1347_);
lean_ctor_set(v___x_1358_, 3, v___x_1357_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v_a_1345_);
lean_ctor_set(v___x_1350_, 0, v___x_1358_);
v___x_1360_ = v___x_1350_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_a_1345_);
v___x_1360_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
v_a_1344_ = v_tail_1348_;
v_a_1345_ = v___x_1360_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__5(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1372_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__4));
v___x_1373_ = lean_unsigned_to_nat(9u);
v___x_1374_ = lean_unsigned_to_nat(355u);
v___x_1375_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__3));
v___x_1376_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__2));
v___x_1377_ = l_mkPanicMessageWithDecl(v___x_1376_, v___x_1375_, v___x_1374_, v___x_1373_, v___x_1372_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1378_, lean_object* v_nFields_x3f_1379_){
_start:
{
if (lean_obj_tag(v_stx_1378_) == 3)
{
lean_object* v_info_1380_; 
v_info_1380_ = lean_ctor_get(v_stx_1378_, 0);
lean_inc(v_info_1380_);
if (lean_obj_tag(v_info_1380_) == 0)
{
lean_object* v_rawVal_1381_; lean_object* v_val_1382_; lean_object* v_leading_1383_; lean_object* v_pos_1384_; lean_object* v_trailing_1385_; lean_object* v_val_1386_; lean_object* v_nameComps_1387_; lean_object* v___y_1392_; lean_object* v_rawComps_1399_; uint8_t v___x_1400_; 
v_rawVal_1381_ = lean_ctor_get(v_stx_1378_, 1);
lean_inc_ref_n(v_rawVal_1381_, 2);
v_val_1382_ = lean_ctor_get(v_stx_1378_, 2);
lean_inc(v_val_1382_);
lean_dec_ref(v_stx_1378_);
v_leading_1383_ = lean_ctor_get(v_info_1380_, 0);
v_pos_1384_ = lean_ctor_get(v_info_1380_, 1);
v_trailing_1385_ = lean_ctor_get(v_info_1380_, 2);
v_val_1386_ = lean_erase_macro_scopes(v_val_1382_);
v_nameComps_1387_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1386_, v_nFields_x3f_1379_);
v_rawComps_1399_ = l_Lean_Syntax_splitNameLit(v_rawVal_1381_);
v___x_1400_ = l_List_isEmpty___redArg(v_rawComps_1399_);
if (v___x_1400_ == 0)
{
if (lean_obj_tag(v_nFields_x3f_1379_) == 1)
{
lean_object* v_val_1401_; lean_object* v_str_1402_; lean_object* v_startPos_1403_; lean_object* v_stopPos_1404_; lean_object* v___x_1405_; lean_object* v_nPrefix_1406_; lean_object* v___y_1408_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_prefixSz_1414_; lean_object* v___x_1415_; lean_object* v_prefixSz_1416_; lean_object* v___y_1418_; uint8_t v___x_1423_; 
v_val_1401_ = lean_ctor_get(v_nFields_x3f_1379_, 0);
v_str_1402_ = lean_ctor_get(v_rawVal_1381_, 0);
v_startPos_1403_ = lean_ctor_get(v_rawVal_1381_, 1);
v_stopPos_1404_ = lean_ctor_get(v_rawVal_1381_, 2);
v___x_1405_ = l_List_lengthTR___redArg(v_rawComps_1399_);
v_nPrefix_1406_ = lean_nat_sub(v___x_1405_, v_val_1401_);
lean_dec(v___x_1405_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
lean_inc(v_nPrefix_1406_);
lean_inc(v_rawComps_1399_);
v___x_1413_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1399_, v_rawComps_1399_, v_nPrefix_1406_, v___x_1412_);
v_prefixSz_1414_ = l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(v___x_1411_, v___x_1413_);
lean_dec(v___x_1413_);
v___x_1415_ = lean_unsigned_to_nat(1u);
v_prefixSz_1416_ = lean_nat_sub(v_prefixSz_1414_, v___x_1415_);
lean_dec(v_prefixSz_1414_);
v___x_1423_ = lean_nat_dec_le(v_prefixSz_1416_, v___x_1411_);
if (v___x_1423_ == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_le(v_stopPos_1404_, v_startPos_1403_);
if (v___x_1424_ == 0)
{
lean_inc(v_startPos_1403_);
v___y_1418_ = v_startPos_1403_;
goto v___jp_1417_;
}
else
{
lean_inc(v_stopPos_1404_);
v___y_1418_ = v_stopPos_1404_;
goto v___jp_1417_;
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_prefixSz_1416_);
v___x_1425_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__1));
v___y_1408_ = v___x_1425_;
goto v___jp_1407_;
}
v___jp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = l_List_drop___redArg(v_nPrefix_1406_, v_rawComps_1399_);
lean_dec(v_rawComps_1399_);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___y_1392_ = v___x_1410_;
goto v___jp_1391_;
}
v___jp_1417_:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_nat_add(v_startPos_1403_, v_prefixSz_1416_);
lean_dec(v_prefixSz_1416_);
v___x_1420_ = lean_nat_dec_le(v_stopPos_1404_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_inc_ref(v_str_1402_);
v___x_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_str_1402_);
lean_ctor_set(v___x_1421_, 1, v___y_1418_);
lean_ctor_set(v___x_1421_, 2, v___x_1419_);
v___y_1408_ = v___x_1421_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1422_; 
lean_dec(v___x_1419_);
lean_inc(v_stopPos_1404_);
lean_inc_ref(v_str_1402_);
v___x_1422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1422_, 0, v_str_1402_);
lean_ctor_set(v___x_1422_, 1, v___y_1418_);
lean_ctor_set(v___x_1422_, 2, v_stopPos_1404_);
v___y_1408_ = v___x_1422_;
goto v___jp_1407_;
}
}
}
else
{
v___y_1392_ = v_rawComps_1399_;
goto v___jp_1391_;
}
}
else
{
lean_dec(v_rawComps_1399_);
lean_dec_ref(v_rawVal_1381_);
goto v___jp_1388_;
}
v___jp_1388_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1380_, v_nameComps_1387_, v___x_1389_);
return v___x_1390_;
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = l_List_lengthTR___redArg(v_nameComps_1387_);
v___x_1394_ = l_List_lengthTR___redArg(v___y_1392_);
v___x_1395_ = lean_nat_dec_eq(v___x_1393_, v___x_1394_);
lean_dec(v___x_1394_);
lean_dec(v___x_1393_);
if (v___x_1395_ == 0)
{
lean_dec(v___y_1392_);
lean_dec_ref(v_rawVal_1381_);
goto v___jp_1388_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc_ref(v_trailing_1385_);
lean_inc(v_pos_1384_);
lean_inc_ref(v_leading_1383_);
lean_dec_ref(v_info_1380_);
v___x_1396_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1387_, v___y_1392_);
v___x_1397_ = lean_box(0);
v___x_1398_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(v_rawVal_1381_, v_pos_1384_, v_trailing_1385_, v_leading_1383_, v___x_1396_, v___x_1397_);
lean_dec(v_pos_1384_);
lean_dec_ref(v_rawVal_1381_);
return v___x_1398_;
}
}
}
else
{
lean_object* v_val_1426_; lean_object* v_val_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_val_1426_ = lean_ctor_get(v_stx_1378_, 2);
lean_inc(v_val_1426_);
lean_dec_ref(v_stx_1378_);
v_val_1427_ = lean_erase_macro_scopes(v_val_1426_);
v___x_1428_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1427_, v_nFields_x3f_1379_);
v___x_1429_ = lean_box(0);
v___x_1430_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1380_, v___x_1428_, v___x_1429_);
return v___x_1430_;
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v_stx_1378_);
v___x_1431_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__5, &l_Lean_Syntax_identComponents___closed__5_once, _init_l_Lean_Syntax_identComponents___closed__5);
v___x_1432_ = l_panic___at___00Lean_Syntax_identComponents_spec__3(v___x_1431_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1433_, lean_object* v_nFields_x3f_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Syntax_identComponents(v_stx_1433_, v_nFields_x3f_1434_);
lean_dec(v_nFields_x3f_1434_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1436_, uint8_t v_firstChoiceOnly_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1438_, 0, v_stx_1436_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*1, v_firstChoiceOnly_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1439_, lean_object* v_firstChoiceOnly_1440_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1441_; lean_object* v_res_1442_; 
v_firstChoiceOnly_boxed_1441_ = lean_unbox(v_firstChoiceOnly_1440_);
v_res_1442_ = l_Lean_Syntax_topDown(v_stx_1439_, v_firstChoiceOnly_boxed_1441_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1443_, lean_object* v_____r_1444_, lean_object* v_b_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1445_);
v___x_1447_ = lean_apply_2(v_toPure_1443_, lean_box(0), v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1448_, lean_object* v_toPure_1449_, lean_object* v_____s_1450_){
_start:
{
lean_object* v_fst_1451_; 
v_fst_1451_ = lean_ctor_get(v_____s_1450_, 0);
if (lean_obj_tag(v_fst_1451_) == 0)
{
lean_object* v_snd_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v_toPure_1449_);
v_snd_1452_ = lean_ctor_get(v_____s_1450_, 1);
lean_inc(v_snd_1452_);
lean_dec_ref(v_____s_1450_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_apply_2(v___f_1448_, v___x_1453_, v_snd_1452_);
return v___x_1454_;
}
else
{
lean_object* v_val_1455_; lean_object* v___x_1456_; 
lean_inc_ref(v_fst_1451_);
lean_dec_ref(v_____s_1450_);
lean_dec(v___f_1448_);
v_val_1455_ = lean_ctor_get(v_fst_1451_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v_fst_1451_);
v___x_1456_ = lean_apply_2(v_toPure_1449_, lean_box(0), v_val_1455_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1457_, lean_object* v_toPure_1458_, lean_object* v___x_1459_, lean_object* v_____do__lift_1460_){
_start:
{
if (lean_obj_tag(v_____do__lift_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v___x_1459_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_____do__lift_1460_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_snd_1457_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = lean_apply_2(v_toPure_1458_, lean_box(0), v___x_1463_);
return v___x_1464_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_snd_1457_);
v_a_1465_ = lean_ctor_get(v_____do__lift_1460_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_____do__lift_1460_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1467_ = v_____do__lift_1460_;
v_isShared_1468_ = v_isSharedCheck_1474_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v_____do__lift_1460_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1474_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1459_);
lean_ctor_set(v___x_1469_, 1, v_a_1465_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_apply_2(v_toPure_1458_, lean_box(0), v___x_1471_);
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1475_, lean_object* v___x_1476_, lean_object* v_inst_1477_, lean_object* v_f_1478_, lean_object* v_firstChoiceOnly_1479_, lean_object* v_toBind_1480_, lean_object* v_a_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1484_; lean_object* v_res_1485_; 
v_firstChoiceOnly_boxed_1484_ = lean_unbox(v_firstChoiceOnly_1479_);
v_res_1485_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1475_, v___x_1476_, v_inst_1477_, v_f_1478_, v_firstChoiceOnly_boxed_1484_, v_toBind_1480_, v_a_1481_, v_x_1482_, v___y_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1489_, lean_object* v_stx_1490_, lean_object* v_inst_1491_, lean_object* v_f_1492_, uint8_t v_firstChoiceOnly_1493_, lean_object* v_toBind_1494_, lean_object* v___f_1495_, lean_object* v___f_1496_, lean_object* v_____do__lift_1497_){
_start:
{
if (lean_obj_tag(v_____do__lift_1497_) == 0)
{
lean_object* v___x_1498_; 
lean_dec(v___f_1496_);
lean_dec(v___f_1495_);
lean_dec(v_toBind_1494_);
lean_dec(v_f_1492_);
lean_dec_ref(v_inst_1491_);
lean_dec(v_stx_1490_);
v___x_1498_ = lean_apply_2(v_toPure_1489_, lean_box(0), v_____do__lift_1497_);
return v___x_1498_;
}
else
{
if (lean_obj_tag(v_stx_1490_) == 1)
{
lean_object* v_a_1499_; lean_object* v_kind_1500_; lean_object* v_args_1501_; 
lean_dec(v___f_1496_);
v_a_1499_ = lean_ctor_get(v_____do__lift_1497_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v_____do__lift_1497_);
v_kind_1500_ = lean_ctor_get(v_stx_1490_, 1);
lean_inc(v_kind_1500_);
v_args_1501_ = lean_ctor_get(v_stx_1490_, 2);
lean_inc_ref(v_args_1501_);
lean_dec_ref(v_stx_1490_);
if (v_firstChoiceOnly_1493_ == 0)
{
lean_dec(v_kind_1500_);
goto v___jp_1502_;
}
else
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1512_ = lean_name_eq(v_kind_1500_, v___x_1511_);
lean_dec(v_kind_1500_);
if (v___x_1512_ == 0)
{
goto v___jp_1502_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec(v___f_1495_);
lean_dec(v_toBind_1494_);
lean_dec(v_toPure_1489_);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = lean_array_get(v___x_1513_, v_args_1501_, v___x_1514_);
lean_dec_ref(v_args_1501_);
v___x_1516_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1491_, v_f_1492_, v_firstChoiceOnly_1493_, v___x_1515_, v_a_1499_);
return v___x_1516_;
}
}
v___jp_1502_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___f_1505_; lean_object* v___x_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_box(v_firstChoiceOnly_1493_);
lean_inc(v_toBind_1494_);
lean_inc_ref(v_inst_1491_);
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1505_, 0, v_toPure_1489_);
lean_closure_set(v___f_1505_, 1, v___x_1503_);
lean_closure_set(v___f_1505_, 2, v_inst_1491_);
lean_closure_set(v___f_1505_, 3, v_f_1492_);
lean_closure_set(v___f_1505_, 4, v___x_1504_);
lean_closure_set(v___f_1505_, 5, v_toBind_1494_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1503_);
lean_ctor_set(v___x_1506_, 1, v_a_1499_);
v_sz_1507_ = lean_array_size(v_args_1501_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1491_, v_args_1501_, v___f_1505_, v_sz_1507_, v___x_1508_, v___x_1506_);
v___x_1510_ = lean_apply_4(v_toBind_1494_, lean_box(0), lean_box(0), v___x_1509_, v___f_1495_);
return v___x_1510_;
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v___f_1495_);
lean_dec(v_toBind_1494_);
lean_dec(v_f_1492_);
lean_dec_ref(v_inst_1491_);
lean_dec(v_stx_1490_);
lean_dec(v_toPure_1489_);
v_a_1517_ = lean_ctor_get(v_____do__lift_1497_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v_____do__lift_1497_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_apply_2(v___f_1496_, v___x_1518_, v_a_1517_);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1520_, lean_object* v_stx_1521_, lean_object* v_inst_1522_, lean_object* v_f_1523_, lean_object* v_firstChoiceOnly_1524_, lean_object* v_toBind_1525_, lean_object* v___f_1526_, lean_object* v___f_1527_, lean_object* v_____do__lift_1528_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1529_; lean_object* v_res_1530_; 
v_firstChoiceOnly_boxed_1529_ = lean_unbox(v_firstChoiceOnly_1524_);
v_res_1530_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1520_, v_stx_1521_, v_inst_1522_, v_f_1523_, v_firstChoiceOnly_boxed_1529_, v_toBind_1525_, v___f_1526_, v___f_1527_, v_____do__lift_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1531_, lean_object* v_f_1532_, uint8_t v_firstChoiceOnly_1533_, lean_object* v_stx_1534_, lean_object* v_b_1535_){
_start:
{
lean_object* v_toApplicative_1536_; lean_object* v_toBind_1537_; lean_object* v_toPure_1538_; lean_object* v___x_1539_; lean_object* v___f_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; 
v_toApplicative_1536_ = lean_ctor_get(v_inst_1531_, 0);
v_toBind_1537_ = lean_ctor_get(v_inst_1531_, 1);
lean_inc_n(v_toBind_1537_, 2);
v_toPure_1538_ = lean_ctor_get(v_toApplicative_1536_, 1);
lean_inc_n(v_toPure_1538_, 3);
lean_inc(v_f_1532_);
lean_inc(v_stx_1534_);
v___x_1539_ = lean_apply_2(v_f_1532_, v_stx_1534_, v_b_1535_);
v___f_1540_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1540_, 0, v_toPure_1538_);
lean_inc_ref(v___f_1540_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1541_, 0, v___f_1540_);
lean_closure_set(v___f_1541_, 1, v_toPure_1538_);
v___x_1542_ = lean_box(v_firstChoiceOnly_1533_);
v___f_1543_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_1543_, 0, v_toPure_1538_);
lean_closure_set(v___f_1543_, 1, v_stx_1534_);
lean_closure_set(v___f_1543_, 2, v_inst_1531_);
lean_closure_set(v___f_1543_, 3, v_f_1532_);
lean_closure_set(v___f_1543_, 4, v___x_1542_);
lean_closure_set(v___f_1543_, 5, v_toBind_1537_);
lean_closure_set(v___f_1543_, 6, v___f_1541_);
lean_closure_set(v___f_1543_, 7, v___f_1540_);
v___x_1544_ = lean_apply_4(v_toBind_1537_, lean_box(0), lean_box(0), v___x_1539_, v___f_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1545_, lean_object* v___x_1546_, lean_object* v_inst_1547_, lean_object* v_f_1548_, uint8_t v_firstChoiceOnly_1549_, lean_object* v_toBind_1550_, lean_object* v_a_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_snd_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_snd_1554_ = lean_ctor_get(v___y_1553_, 1);
lean_inc_n(v_snd_1554_, 2);
lean_dec_ref(v___y_1553_);
v___f_1555_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1555_, 0, v_snd_1554_);
lean_closure_set(v___f_1555_, 1, v_toPure_1545_);
lean_closure_set(v___f_1555_, 2, v___x_1546_);
v___x_1556_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1547_, v_f_1548_, v_firstChoiceOnly_1549_, v_a_1551_, v_snd_1554_);
v___x_1557_ = lean_apply_4(v_toBind_1550_, lean_box(0), lean_box(0), v___x_1556_, v___f_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_firstChoiceOnly_1560_, lean_object* v_stx_1561_, lean_object* v_b_1562_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1563_; lean_object* v_res_1564_; 
v_firstChoiceOnly_boxed_1563_ = lean_unbox(v_firstChoiceOnly_1560_);
v_res_1564_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1558_, v_f_1559_, v_firstChoiceOnly_boxed_1563_, v_stx_1561_, v_b_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1565_, lean_object* v_inst_1566_, lean_object* v_00_u03b2_1567_, lean_object* v_f_1568_, uint8_t v_firstChoiceOnly_1569_, lean_object* v_stx_1570_, lean_object* v_b_1571_, lean_object* v_inst_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1566_, v_f_1568_, v_firstChoiceOnly_1569_, v_stx_1570_, v_b_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1574_, lean_object* v_inst_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_f_1577_, lean_object* v_firstChoiceOnly_1578_, lean_object* v_stx_1579_, lean_object* v_b_1580_, lean_object* v_inst_1581_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1582_; lean_object* v_res_1583_; 
v_firstChoiceOnly_boxed_1582_ = lean_unbox(v_firstChoiceOnly_1578_);
v_res_1583_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1574_, v_inst_1575_, v_00_u03b2_1576_, v_f_1577_, v_firstChoiceOnly_boxed_1582_, v_stx_1579_, v_b_1580_, v_inst_1581_);
lean_dec(v_inst_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1584_, lean_object* v_____do__lift_1585_){
_start:
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v_____do__lift_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v_____do__lift_1585_);
v___x_1587_ = lean_apply_2(v_toPure_1584_, lean_box(0), v_a_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1588_, lean_object* v_toBind_1589_, lean_object* v___f_1590_, lean_object* v_00_u03b2_1591_, lean_object* v_x_1592_, lean_object* v_init_1593_, lean_object* v_f_1594_){
_start:
{
uint8_t v_firstChoiceOnly_1595_; lean_object* v_stx_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_firstChoiceOnly_1595_ = lean_ctor_get_uint8(v_x_1592_, sizeof(void*)*1);
v_stx_1596_ = lean_ctor_get(v_x_1592_, 0);
lean_inc(v_stx_1596_);
lean_dec_ref(v_x_1592_);
v___x_1597_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1588_, v_f_1594_, v_firstChoiceOnly_1595_, v_stx_1596_, v_init_1593_);
v___x_1598_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1597_, v___f_1590_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1599_){
_start:
{
lean_object* v_toApplicative_1600_; lean_object* v_toBind_1601_; lean_object* v_toPure_1602_; lean_object* v___f_1603_; lean_object* v___f_1604_; 
v_toApplicative_1600_ = lean_ctor_get(v_inst_1599_, 0);
v_toBind_1601_ = lean_ctor_get(v_inst_1599_, 1);
lean_inc(v_toBind_1601_);
v_toPure_1602_ = lean_ctor_get(v_toApplicative_1600_, 1);
lean_inc(v_toPure_1602_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1603_, 0, v_toPure_1602_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1604_, 0, v_inst_1599_);
lean_closure_set(v___f_1604_, 1, v_toBind_1601_);
lean_closure_set(v___f_1604_, 2, v___f_1603_);
return v___f_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1605_, lean_object* v_inst_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1609_, lean_object* v_val_1610_){
_start:
{
if (lean_obj_tag(v_info_1609_) == 0)
{
lean_object* v_leading_1611_; lean_object* v_trailing_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_leading_1611_ = lean_ctor_get(v_info_1609_, 0);
lean_inc_ref(v_leading_1611_);
v_trailing_1612_ = lean_ctor_get(v_info_1609_, 2);
lean_inc_ref(v_trailing_1612_);
lean_dec_ref(v_info_1609_);
v___x_1613_ = lean_substring_tostring(v_leading_1611_);
v___x_1614_ = lean_string_append(v___x_1613_, v_val_1610_);
v___x_1615_ = lean_substring_tostring(v_trailing_1612_);
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
lean_dec_ref(v___x_1615_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_info_1609_);
v___x_1617_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1618_ = lean_string_append(v___x_1617_, v_val_1610_);
v___x_1619_ = lean_string_append(v___x_1618_, v___x_1617_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1620_, lean_object* v_val_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1620_, v_val_1621_);
lean_dec_ref(v_val_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1623_, lean_object* v_as_1624_, size_t v_sz_1625_, size_t v_i_1626_, lean_object* v_b_1627_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_usize_dec_lt(v_i_1626_, v_sz_1625_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_b_1627_);
return v___x_1629_;
}
else
{
lean_object* v_snd_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1657_; 
v_snd_1630_ = lean_ctor_get(v_b_1627_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_b_1627_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_b_1627_, 0);
lean_dec(v_unused_1658_);
v___x_1632_ = v_b_1627_;
v_isShared_1633_ = v_isSharedCheck_1657_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_snd_1630_);
lean_dec(v_b_1627_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1657_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_array_uget_borrowed(v_as_1624_, v_i_1626_);
lean_inc(v_snd_1630_);
lean_inc(v_a_1634_);
v___x_1635_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1623_, v_a_1634_, v_snd_1630_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_del_object(v___x_1632_);
lean_dec(v_snd_1630_);
v___x_1636_ = lean_box(0);
return v___x_1636_;
}
else
{
lean_object* v_val_1637_; 
v_val_1637_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1637_);
if (lean_obj_tag(v_val_1637_) == 0)
{
lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v_val_1637_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_val_1637_, 0);
lean_dec(v_unused_1648_);
v___x_1639_ = v_val_1637_;
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
else
{
lean_dec(v_val_1637_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1635_);
v___x_1642_ = v___x_1632_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_snd_1630_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set_tag(v___x_1639_, 1);
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
lean_dec_ref(v___x_1635_);
lean_dec(v_snd_1630_);
v_a_1649_ = lean_ctor_get(v_val_1637_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v_val_1637_);
v___x_1650_ = lean_box(0);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v_a_1649_);
lean_ctor_set(v___x_1632_, 0, v___x_1650_);
v___x_1652_ = v___x_1632_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_a_1649_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
size_t v___x_1653_; size_t v___x_1654_; 
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_add(v_i_1626_, v___x_1653_);
v_i_1626_ = v___x_1654_;
v_b_1627_ = v___x_1652_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_){
_start:
{
lean_object* v_array_1662_; lean_object* v_start_1663_; lean_object* v_stop_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1683_; 
v_array_1662_ = lean_ctor_get(v_a_1660_, 0);
v_start_1663_ = lean_ctor_get(v_a_1660_, 1);
v_stop_1664_ = lean_ctor_get(v_a_1660_, 2);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1666_ = v_a_1660_;
v_isShared_1667_ = v_isSharedCheck_1683_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_stop_1664_);
lean_inc(v_start_1663_);
lean_inc(v_array_1662_);
lean_dec(v_a_1660_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1683_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_lt(v_start_1663_, v_stop_1664_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_del_object(v___x_1666_);
lean_dec(v_stop_1664_);
lean_dec(v_start_1663_);
lean_dec_ref(v_array_1662_);
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1661_);
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_array_fget_borrowed(v_array_1662_, v_start_1663_);
lean_inc(v___x_1670_);
v___x_1671_ = l_Lean_Syntax_reprint(v___x_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1672_; 
lean_del_object(v___x_1666_);
lean_dec(v_stop_1664_);
lean_dec(v_start_1663_);
lean_dec_ref(v_array_1662_);
v___x_1672_ = lean_box(0);
return v___x_1672_;
}
else
{
lean_object* v_val_1673_; uint8_t v___x_1674_; 
v_val_1673_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_val_1673_);
lean_dec_ref(v___x_1671_);
v___x_1674_ = lean_string_dec_eq(v_val_1659_, v_val_1673_);
lean_dec(v_val_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
lean_del_object(v___x_1666_);
lean_dec(v_stop_1664_);
lean_dec(v_start_1663_);
lean_dec_ref(v_array_1662_);
v___x_1675_ = lean_box(0);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_add(v_start_1663_, v___x_1677_);
lean_dec(v_start_1663_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1678_);
v___x_1680_ = v___x_1666_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_array_1662_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_stop_1664_);
v___x_1680_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v_a_1660_ = v___x_1680_;
v_b_1661_ = v___x_1676_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1684_, lean_object* v_stx_1685_, lean_object* v_b_1686_){
_start:
{
lean_object* v_b_1688_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v_a_1703_; 
switch(lean_obj_tag(v_stx_1685_))
{
case 2:
{
lean_object* v_info_1713_; lean_object* v_val_1714_; lean_object* v___x_1715_; lean_object* v_s_1716_; 
v_info_1713_ = lean_ctor_get(v_stx_1685_, 0);
v_val_1714_ = lean_ctor_get(v_stx_1685_, 1);
lean_inc(v_info_1713_);
v___x_1715_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1713_, v_val_1714_);
v_s_1716_ = lean_string_append(v_b_1686_, v___x_1715_);
lean_dec_ref(v___x_1715_);
v_a_1703_ = v_s_1716_;
goto v___jp_1702_;
}
case 3:
{
lean_object* v_rawVal_1717_; lean_object* v_info_1718_; lean_object* v_str_1719_; lean_object* v_startPos_1720_; lean_object* v_stopPos_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v_s_1724_; 
v_rawVal_1717_ = lean_ctor_get(v_stx_1685_, 1);
v_info_1718_ = lean_ctor_get(v_stx_1685_, 0);
v_str_1719_ = lean_ctor_get(v_rawVal_1717_, 0);
v_startPos_1720_ = lean_ctor_get(v_rawVal_1717_, 1);
v_stopPos_1721_ = lean_ctor_get(v_rawVal_1717_, 2);
v___x_1722_ = lean_string_utf8_extract(v_str_1719_, v_startPos_1720_, v_stopPos_1721_);
lean_inc(v_info_1718_);
v___x_1723_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1718_, v___x_1722_);
lean_dec_ref(v___x_1722_);
v_s_1724_ = lean_string_append(v_b_1686_, v___x_1723_);
lean_dec_ref(v___x_1723_);
v_a_1703_ = v_s_1724_;
goto v___jp_1702_;
}
case 1:
{
lean_object* v_kind_1725_; lean_object* v_args_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_kind_1725_ = lean_ctor_get(v_stx_1685_, 1);
v_args_1726_ = lean_ctor_get(v_stx_1685_, 2);
v___x_1727_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1728_ = lean_name_eq(v_kind_1725_, v___x_1727_);
if (v___x_1728_ == 0)
{
v_a_1703_ = v_b_1686_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = lean_array_get_borrowed(v___x_1729_, v_args_1726_, v___x_1730_);
lean_inc(v___x_1731_);
v___x_1732_ = l_Lean_Syntax_reprint(v___x_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref(v_stx_1685_);
lean_dec_ref(v_b_1686_);
v___x_1733_ = lean_box(0);
return v___x_1733_;
}
else
{
lean_object* v_val_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_val_1734_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_val_1734_);
lean_dec_ref(v___x_1732_);
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_array_get_size(v_args_1726_);
lean_inc_ref(v_args_1726_);
v___x_1737_ = l_Array_toSubarray___redArg(v_args_1726_, v___x_1735_, v___x_1736_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1734_, v___x_1737_, v___x_1738_);
lean_dec(v_val_1734_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v_stx_1685_);
lean_dec_ref(v_b_1686_);
v___x_1740_ = lean_box(0);
return v___x_1740_;
}
else
{
lean_dec_ref(v___x_1739_);
v_a_1703_ = v_b_1686_;
goto v___jp_1702_;
}
}
}
}
default: 
{
v_a_1703_ = v_b_1686_;
goto v___jp_1702_;
}
}
v___jp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_b_1688_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
v___jp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; size_t v_sz_1696_; size_t v___x_1697_; lean_object* v___x_1698_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___y_1693_);
v_sz_1696_ = lean_array_size(v___y_1692_);
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1684_, v___y_1692_, v_sz_1696_, v___x_1697_, v___x_1695_);
lean_dec_ref(v___y_1692_);
if (lean_obj_tag(v___x_1698_) == 0)
{
return v___x_1694_;
}
else
{
lean_object* v_val_1699_; lean_object* v_fst_1700_; 
v_val_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1699_);
lean_dec_ref(v___x_1698_);
v_fst_1700_ = lean_ctor_get(v_val_1699_, 0);
if (lean_obj_tag(v_fst_1700_) == 0)
{
lean_object* v_snd_1701_; 
v_snd_1701_ = lean_ctor_get(v_val_1699_, 1);
lean_inc(v_snd_1701_);
lean_dec(v_val_1699_);
v_b_1688_ = v_snd_1701_;
goto v___jp_1687_;
}
else
{
lean_inc_ref(v_fst_1700_);
lean_dec(v_val_1699_);
return v_fst_1700_;
}
}
}
v___jp_1702_:
{
if (lean_obj_tag(v_stx_1685_) == 1)
{
if (v_firstChoiceOnly_1684_ == 0)
{
lean_object* v_args_1704_; 
v_args_1704_ = lean_ctor_get(v_stx_1685_, 2);
lean_inc_ref(v_args_1704_);
lean_dec_ref(v_stx_1685_);
v___y_1692_ = v_args_1704_;
v___y_1693_ = v_a_1703_;
goto v___jp_1691_;
}
else
{
lean_object* v_kind_1705_; lean_object* v_args_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_kind_1705_ = lean_ctor_get(v_stx_1685_, 1);
lean_inc(v_kind_1705_);
v_args_1706_ = lean_ctor_get(v_stx_1685_, 2);
lean_inc_ref(v_args_1706_);
lean_dec_ref(v_stx_1685_);
v___x_1707_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1708_ = lean_name_eq(v_kind_1705_, v___x_1707_);
lean_dec(v_kind_1705_);
if (v___x_1708_ == 0)
{
v___y_1692_ = v_args_1706_;
v___y_1693_ = v_a_1703_;
goto v___jp_1691_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get(v___x_1709_, v_args_1706_, v___x_1710_);
lean_dec_ref(v_args_1706_);
v_stx_1685_ = v___x_1711_;
v_b_1686_ = v_a_1703_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1685_);
v_b_1688_ = v_a_1703_;
goto v___jp_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1741_){
_start:
{
lean_object* v_s_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; 
v_s_1742_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1743_ = 1;
v___x_1744_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1743_, v_stx_1741_, v_s_1742_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_box(0);
return v___x_1745_;
}
else
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
v_val_1746_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1748_ = v___x_1744_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v___x_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_a_1750_; lean_object* v___x_1752_; 
v_a_1750_ = lean_ctor_get(v_val_1746_, 0);
lean_inc(v_a_1750_);
lean_dec(v_val_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v_a_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1755_, lean_object* v_a_1756_, lean_object* v_b_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1755_, v_a_1756_, v_b_1757_);
lean_dec_ref(v_val_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1759_, lean_object* v_as_1760_, lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_b_1763_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1764_; size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v_firstChoiceOnly_boxed_1764_ = lean_unbox(v_firstChoiceOnly_1759_);
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1764_, v_as_1760_, v_sz_boxed_1765_, v_i_boxed_1766_, v_b_1763_);
lean_dec_ref(v_as_1760_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1768_, lean_object* v_stx_1769_, lean_object* v_b_1770_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1771_; lean_object* v_res_1772_; 
v_firstChoiceOnly_boxed_1771_ = lean_unbox(v_firstChoiceOnly_1768_);
v_res_1772_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1771_, v_stx_1769_, v_b_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1773_, lean_object* v_inst_1774_, lean_object* v_R_1775_, lean_object* v_a_1776_, lean_object* v_b_1777_, lean_object* v_c_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1773_, v_a_1776_, v_b_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1780_, lean_object* v_inst_1781_, lean_object* v_R_1782_, lean_object* v_a_1783_, lean_object* v_b_1784_, lean_object* v_c_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1780_, v_inst_1781_, v_R_1782_, v_a_1783_, v_b_1784_, v_c_1785_);
lean_dec_ref(v_val_1780_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1795_, lean_object* v_stx_1796_){
_start:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = lean_box(0);
v___x_1798_ = l_Lean_Syntax_isMissing(v_stx_1796_);
if (v___x_1798_ == 0)
{
if (lean_obj_tag(v_stx_1796_) == 1)
{
lean_object* v_kind_1799_; lean_object* v_args_1800_; 
v_kind_1799_ = lean_ctor_get(v_stx_1796_, 1);
v_args_1800_ = lean_ctor_get(v_stx_1796_, 2);
if (v_firstChoiceOnly_1795_ == 0)
{
goto v___jp_1801_;
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1811_ = lean_name_eq(v_kind_1799_, v___x_1810_);
if (v___x_1811_ == 0)
{
goto v___jp_1801_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_borrowed(v___x_1812_, v_args_1800_, v___x_1813_);
v_stx_1796_ = v___x_1814_;
goto _start;
}
}
v___jp_1801_:
{
lean_object* v___x_1802_; size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_1805_; lean_object* v_fst_1806_; 
v___x_1802_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1803_ = lean_array_size(v_args_1800_);
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1795_, v_args_1800_, v_sz_1803_, v___x_1804_, v___x_1802_);
v_fst_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_fst_1806_);
if (lean_obj_tag(v_fst_1806_) == 0)
{
lean_object* v_snd_1807_; lean_object* v___x_1808_; 
v_snd_1807_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1805_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_snd_1807_);
return v___x_1808_;
}
else
{
lean_object* v_val_1809_; 
lean_dec_ref(v___x_1805_);
v_val_1809_ = lean_ctor_get(v_fst_1806_, 0);
lean_inc(v_val_1809_);
lean_dec_ref(v_fst_1806_);
return v_val_1809_;
}
}
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1816_;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1817_ = lean_box(v___x_1798_);
v___x_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1797_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1821_, lean_object* v_as_1822_, size_t v_sz_1823_, size_t v_i_1824_, lean_object* v_b_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_usize_dec_lt(v_i_1824_, v_sz_1823_);
if (v___x_1826_ == 0)
{
return v_b_1825_;
}
else
{
lean_object* v_snd_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1845_; 
v_snd_1827_ = lean_ctor_get(v_b_1825_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_b_1825_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; 
v_unused_1846_ = lean_ctor_get(v_b_1825_, 0);
lean_dec(v_unused_1846_);
v___x_1829_ = v_b_1825_;
v_isShared_1830_ = v_isSharedCheck_1845_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snd_1827_);
lean_dec(v_b_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1845_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_array_uget_borrowed(v_as_1822_, v_i_1824_);
v___x_1832_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1821_, v_a_1831_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1833_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_snd_1827_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_dec(v_snd_1827_);
v_a_1837_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1832_);
v___x_1838_ = lean_box(0);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v_a_1837_);
lean_ctor_set(v___x_1829_, 0, v___x_1838_);
v___x_1840_ = v___x_1829_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_a_1837_);
v___x_1840_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
size_t v___x_1841_; size_t v___x_1842_; 
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_add(v_i_1824_, v___x_1841_);
v_i_1824_ = v___x_1842_;
v_b_1825_ = v___x_1840_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1847_, lean_object* v_as_1848_, lean_object* v_sz_1849_, lean_object* v_i_1850_, lean_object* v_b_1851_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1852_; size_t v_sz_boxed_1853_; size_t v_i_boxed_1854_; lean_object* v_res_1855_; 
v_firstChoiceOnly_boxed_1852_ = lean_unbox(v_firstChoiceOnly_1847_);
v_sz_boxed_1853_ = lean_unbox_usize(v_sz_1849_);
lean_dec(v_sz_1849_);
v_i_boxed_1854_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1852_, v_as_1848_, v_sz_boxed_1853_, v_i_boxed_1854_, v_b_1851_);
lean_dec_ref(v_as_1848_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1856_, lean_object* v_stx_1857_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1858_; lean_object* v_res_1859_; 
v_firstChoiceOnly_boxed_1858_ = lean_unbox(v_firstChoiceOnly_1856_);
v_res_1859_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1858_, v_stx_1857_);
lean_dec(v_stx_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1860_){
_start:
{
uint8_t v___x_1861_; lean_object* v___y_1863_; lean_object* v___x_1867_; lean_object* v_a_1868_; 
v___x_1861_ = 0;
v___x_1867_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1861_, v_stx_1860_);
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
v___y_1863_ = v_a_1868_;
goto v___jp_1862_;
v___jp_1862_:
{
lean_object* v_fst_1864_; 
v_fst_1864_ = lean_ctor_get(v___y_1863_, 0);
lean_inc(v_fst_1864_);
lean_dec_ref(v___y_1863_);
if (lean_obj_tag(v_fst_1864_) == 0)
{
return v___x_1861_;
}
else
{
lean_object* v_val_1865_; uint8_t v___x_1866_; 
v_val_1865_ = lean_ctor_get(v_fst_1864_, 0);
lean_inc(v_val_1865_);
lean_dec_ref(v_fst_1864_);
v___x_1866_ = lean_unbox(v_val_1865_);
lean_dec(v_val_1865_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1869_){
_start:
{
uint8_t v_res_1870_; lean_object* v_r_1871_; 
v_res_1870_ = l_Lean_Syntax_hasMissing(v_stx_1869_);
lean_dec(v_stx_1869_);
v_r_1871_ = lean_box(v_res_1870_);
return v_r_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1872_, lean_object* v_stx_1873_, lean_object* v_b_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1872_, v_stx_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1876_, lean_object* v_stx_1877_, lean_object* v_b_1878_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1879_; lean_object* v_res_1880_; 
v_firstChoiceOnly_boxed_1879_ = lean_unbox(v_firstChoiceOnly_1876_);
v_res_1880_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1879_, v_stx_1877_, v_b_1878_);
lean_dec_ref(v_b_1878_);
lean_dec(v_stx_1877_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1881_, uint8_t v_canonicalOnly_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Syntax_getPos_x3f(v_stx_1881_, v_canonicalOnly_1882_);
if (lean_obj_tag(v___x_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1885_; 
v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_val_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1881_, v_canonicalOnly_1882_);
if (lean_obj_tag(v___x_1885_) == 1)
{
lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
v_val_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_val_1884_);
lean_ctor_set(v___x_1890_, 1, v_val_1886_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
lean_object* v___x_1895_; 
lean_dec(v___x_1885_);
lean_dec(v_val_1884_);
v___x_1895_ = lean_box(0);
return v___x_1895_;
}
}
else
{
lean_object* v___x_1896_; 
lean_dec(v___x_1883_);
v___x_1896_ = lean_box(0);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1897_, lean_object* v_canonicalOnly_1898_){
_start:
{
uint8_t v_canonicalOnly_boxed_1899_; lean_object* v_res_1900_; 
v_canonicalOnly_boxed_1899_ = lean_unbox(v_canonicalOnly_1898_);
v_res_1900_ = l_Lean_Syntax_getRange_x3f(v_stx_1897_, v_canonicalOnly_boxed_1899_);
lean_dec(v_stx_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1901_, uint8_t v_canonicalOnly_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Syntax_getPos_x3f(v_stx_1901_, v_canonicalOnly_1902_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_box(0);
return v___x_1904_;
}
else
{
lean_object* v_val_1905_; lean_object* v___x_1906_; 
v_val_1905_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_val_1905_);
lean_dec_ref(v___x_1903_);
v___x_1906_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1901_, v_canonicalOnly_1902_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; 
lean_dec(v_val_1905_);
v___x_1907_ = lean_box(0);
return v___x_1907_;
}
else
{
lean_object* v_val_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1916_; 
v_val_1908_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1910_ = v___x_1906_;
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_val_1908_);
lean_dec(v___x_1906_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_val_1905_);
lean_ctor_set(v___x_1912_, 1, v_val_1908_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1917_, lean_object* v_canonicalOnly_1918_){
_start:
{
uint8_t v_canonicalOnly_boxed_1919_; lean_object* v_res_1920_; 
v_canonicalOnly_boxed_1919_ = lean_unbox(v_canonicalOnly_1918_);
v_res_1920_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1917_, v_canonicalOnly_boxed_1919_);
lean_dec(v_stx_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1921_, uint8_t v_canonical_1922_){
_start:
{
lean_object* v_start_1923_; lean_object* v_stop_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1933_; 
v_start_1923_ = lean_ctor_get(v_range_1921_, 0);
v_stop_1924_ = lean_ctor_get(v_range_1921_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_range_1921_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1926_ = v_range_1921_;
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_stop_1924_);
lean_inc(v_start_1923_);
lean_dec(v_range_1921_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1928_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1928_, 0, v_start_1923_);
lean_ctor_set(v___x_1928_, 1, v_stop_1924_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*2, v_canonical_1922_);
v___x_1929_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 2);
lean_ctor_set(v___x_1926_, 1, v___x_1929_);
lean_ctor_set(v___x_1926_, 0, v___x_1928_);
v___x_1931_ = v___x_1926_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_1934_, lean_object* v_canonical_1935_){
_start:
{
uint8_t v_canonical_boxed_1936_; lean_object* v_res_1937_; 
v_canonical_boxed_1936_ = lean_unbox(v_canonical_1935_);
v_res_1937_ = l_Lean_Syntax_ofRange(v_range_1934_, v_canonical_boxed_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_1940_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_1942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1942_, 0, v_stx_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
lean_ctor_set(v___x_1942_, 2, v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_1943_, lean_object* v_stx_1944_){
_start:
{
lean_object* v_parents_1945_; lean_object* v_idxs_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_parents_1945_ = lean_ctor_get(v_t_1943_, 1);
v_idxs_1946_ = lean_ctor_get(v_t_1943_, 2);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_t_1943_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v_t_1943_, 0);
lean_dec(v_unused_1954_);
v___x_1948_ = v_t_1943_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_idxs_1946_);
lean_inc(v_parents_1945_);
lean_dec(v_t_1943_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v_stx_1944_);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_stx_1944_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_parents_1945_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_idxs_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_1955_, lean_object* v_idx_1956_){
_start:
{
lean_object* v_cur_1957_; lean_object* v_parents_1958_; lean_object* v_idxs_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1979_; 
v_cur_1957_ = lean_ctor_get(v_t_1955_, 0);
v_parents_1958_ = lean_ctor_get(v_t_1955_, 1);
v_idxs_1959_ = lean_ctor_get(v_t_1955_, 2);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_t_1955_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1961_ = v_t_1955_;
v_isShared_1962_ = v_isSharedCheck_1979_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_idxs_1959_);
lean_inc(v_parents_1958_);
lean_inc(v_cur_1957_);
lean_dec(v_t_1955_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1979_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = l_Lean_Syntax_getNumArgs(v_cur_1957_);
v___x_1964_ = lean_nat_dec_lt(v_idx_1956_, v___x_1963_);
lean_dec(v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_array_push(v_parents_1958_, v_cur_1957_);
v___x_1967_ = lean_array_push(v_idxs_1959_, v_idx_1956_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 2, v___x_1967_);
lean_ctor_set(v___x_1961_, 1, v___x_1966_);
lean_ctor_set(v___x_1961_, 0, v___x_1965_);
v___x_1969_ = v___x_1961_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1971_ = l_Lean_Syntax_getArg(v_cur_1957_, v_idx_1956_);
v___x_1972_ = lean_box(0);
v___x_1973_ = l_Lean_Syntax_setArg(v_cur_1957_, v_idx_1956_, v___x_1972_);
v___x_1974_ = lean_array_push(v_parents_1958_, v___x_1973_);
v___x_1975_ = lean_array_push(v_idxs_1959_, v_idx_1956_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 2, v___x_1975_);
lean_ctor_set(v___x_1961_, 1, v___x_1974_);
lean_ctor_set(v___x_1961_, 0, v___x_1971_);
v___x_1977_ = v___x_1961_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_1980_){
_start:
{
lean_object* v_cur_1981_; lean_object* v_parents_1982_; lean_object* v_idxs_1983_; lean_object* v___y_1985_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_cur_1981_ = lean_ctor_get(v_t_1980_, 0);
v_parents_1982_ = lean_ctor_get(v_t_1980_, 1);
v_idxs_1983_ = lean_ctor_get(v_t_1980_, 2);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_array_get_size(v_parents_1982_);
v___x_1991_ = lean_nat_dec_lt(v___x_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
return v_t_1980_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
lean_inc_ref(v_idxs_1983_);
lean_inc_ref(v_parents_1982_);
lean_inc(v_cur_1981_);
lean_dec_ref(v_t_1980_);
v___x_1992_ = lean_array_get_size(v_idxs_1983_);
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_nat_sub(v___x_1992_, v___x_1993_);
v___x_1995_ = lean_array_get_borrowed(v___x_1989_, v_idxs_1983_, v___x_1994_);
lean_dec(v___x_1994_);
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_nat_sub(v___x_1990_, v___x_1993_);
v___x_1998_ = lean_array_get_borrowed(v___x_1996_, v_parents_1982_, v___x_1997_);
lean_dec(v___x_1997_);
v___x_1999_ = l_Lean_Syntax_getNumArgs(v___x_1998_);
v___x_2000_ = lean_nat_dec_lt(v___x_1995_, v___x_1999_);
lean_dec(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec(v_cur_1981_);
lean_inc(v___x_1998_);
v___y_1985_ = v___x_1998_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2001_; 
lean_inc(v___x_1998_);
v___x_2001_ = l_Lean_Syntax_setArg(v___x_1998_, v___x_1995_, v_cur_1981_);
v___y_1985_ = v___x_2001_;
goto v___jp_1984_;
}
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_array_pop(v_parents_1982_);
v___x_1987_ = lean_array_pop(v_idxs_1983_);
v___x_1988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1988_, 0, v___y_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1986_);
lean_ctor_set(v___x_1988_, 2, v___x_1987_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2002_){
_start:
{
lean_object* v_parents_2003_; lean_object* v_idxs_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_parents_2003_ = lean_ctor_get(v_t_2002_, 1);
v_idxs_2004_ = lean_ctor_get(v_t_2002_, 2);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_array_get_size(v_parents_2003_);
v___x_2007_ = lean_nat_dec_lt(v___x_2005_, v___x_2006_);
if (v___x_2007_ == 0)
{
return v_t_2002_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_inc_ref(v_idxs_2004_);
v___x_2008_ = l_Lean_Syntax_Traverser_up(v_t_2002_);
v___x_2009_ = lean_array_get_size(v_idxs_2004_);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_sub(v___x_2009_, v___x_2010_);
v___x_2012_ = lean_array_get(v___x_2005_, v_idxs_2004_, v___x_2011_);
lean_dec(v___x_2011_);
lean_dec_ref(v_idxs_2004_);
v___x_2013_ = lean_nat_sub(v___x_2012_, v___x_2010_);
lean_dec(v___x_2012_);
v___x_2014_ = l_Lean_Syntax_Traverser_down(v___x_2008_, v___x_2013_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2015_){
_start:
{
lean_object* v_parents_2016_; lean_object* v_idxs_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_parents_2016_ = lean_ctor_get(v_t_2015_, 1);
v_idxs_2017_ = lean_ctor_get(v_t_2015_, 2);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_array_get_size(v_parents_2016_);
v___x_2020_ = lean_nat_dec_lt(v___x_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v_t_2015_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_inc_ref(v_idxs_2017_);
v___x_2021_ = l_Lean_Syntax_Traverser_up(v_t_2015_);
v___x_2022_ = lean_array_get_size(v_idxs_2017_);
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_sub(v___x_2022_, v___x_2023_);
v___x_2025_ = lean_array_get(v___x_2018_, v_idxs_2017_, v___x_2024_);
lean_dec(v___x_2024_);
lean_dec_ref(v_idxs_2017_);
v___x_2026_ = lean_nat_add(v___x_2025_, v___x_2023_);
lean_dec(v___x_2025_);
v___x_2027_ = l_Lean_Syntax_Traverser_down(v___x_2021_, v___x_2026_);
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2028_){
_start:
{
lean_object* v_cur_2029_; 
v_cur_2029_ = lean_ctor_get(v_self_2028_, 0);
lean_inc(v_cur_2029_);
return v_cur_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2030_);
lean_dec_ref(v_self_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2033_, lean_object* v_t_2034_){
_start:
{
lean_object* v_toApplicative_2035_; lean_object* v_toFunctor_2036_; lean_object* v_map_2037_; lean_object* v_get_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; 
v_toApplicative_2035_ = lean_ctor_get(v_inst_2033_, 0);
lean_inc_ref(v_toApplicative_2035_);
lean_dec_ref(v_inst_2033_);
v_toFunctor_2036_ = lean_ctor_get(v_toApplicative_2035_, 0);
lean_inc_ref(v_toFunctor_2036_);
lean_dec_ref(v_toApplicative_2035_);
v_map_2037_ = lean_ctor_get(v_toFunctor_2036_, 0);
lean_inc(v_map_2037_);
lean_dec_ref(v_toFunctor_2036_);
v_get_2038_ = lean_ctor_get(v_t_2034_, 0);
lean_inc(v_get_2038_);
lean_dec_ref(v_t_2034_);
v___f_2039_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2040_ = lean_apply_4(v_map_2037_, lean_box(0), lean_box(0), v___f_2039_, v_get_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2041_, lean_object* v_inst_2042_, lean_object* v_t_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2042_, v_t_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2045_, lean_object* v_s_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_Syntax_Traverser_setCur(v_s_2046_, v_stx_2045_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2050_, lean_object* v_stx_2051_){
_start:
{
lean_object* v_modifyGet_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; 
v_modifyGet_2052_ = lean_ctor_get(v_t_2050_, 2);
lean_inc(v_modifyGet_2052_);
lean_dec_ref(v_t_2050_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2053_, 0, v_stx_2051_);
v___x_2054_ = lean_apply_2(v_modifyGet_2052_, lean_box(0), v___f_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2055_, lean_object* v_t_2056_, lean_object* v_stx_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2056_, v_stx_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2059_, lean_object* v_s_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Lean_Syntax_Traverser_down(v_s_2060_, v_idx_2059_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2064_, lean_object* v_idx_2065_){
_start:
{
lean_object* v_modifyGet_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; 
v_modifyGet_2066_ = lean_ctor_get(v_t_2064_, 2);
lean_inc(v_modifyGet_2066_);
lean_dec_ref(v_t_2064_);
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2067_, 0, v_idx_2065_);
v___x_2068_ = lean_apply_2(v_modifyGet_2066_, lean_box(0), v___f_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2069_, lean_object* v_t_2070_, lean_object* v_idx_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2070_, v_idx_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2073_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Lean_Syntax_Traverser_up(v_s_2073_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2078_){
_start:
{
lean_object* v_modifyGet_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; 
v_modifyGet_2079_ = lean_ctor_get(v_t_2078_, 2);
lean_inc(v_modifyGet_2079_);
lean_dec_ref(v_t_2078_);
v___f_2080_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2081_ = lean_apply_2(v_modifyGet_2079_, lean_box(0), v___f_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2082_, lean_object* v_t_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_box(0);
v___x_2087_ = l_Lean_Syntax_Traverser_left(v_s_2085_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2090_){
_start:
{
lean_object* v_modifyGet_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; 
v_modifyGet_2091_ = lean_ctor_get(v_t_2090_, 2);
lean_inc(v_modifyGet_2091_);
lean_dec_ref(v_t_2090_);
v___f_2092_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2093_ = lean_apply_2(v_modifyGet_2091_, lean_box(0), v___f_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2094_, lean_object* v_t_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = l_Lean_Syntax_Traverser_right(v_s_2097_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2102_){
_start:
{
lean_object* v_modifyGet_2103_; lean_object* v___f_2104_; lean_object* v___x_2105_; 
v_modifyGet_2103_ = lean_ctor_get(v_t_2102_, 2);
lean_inc(v_modifyGet_2103_);
lean_dec_ref(v_t_2102_);
v___f_2104_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2105_ = lean_apply_2(v_modifyGet_2103_, lean_box(0), v___f_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2106_, lean_object* v_t_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2109_, lean_object* v_st_2110_){
_start:
{
lean_object* v_idxs_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_idxs_2111_ = lean_ctor_get(v_st_2110_, 2);
v___x_2112_ = lean_array_get_size(v_idxs_2111_);
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_sub(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_nat_dec_lt(v___x_2114_, v___x_2112_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v___x_2114_);
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_apply_2(v_toPure_2109_, lean_box(0), v___x_2116_);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_array_fget_borrowed(v_idxs_2111_, v___x_2114_);
lean_dec(v___x_2114_);
lean_inc(v___x_2118_);
v___x_2119_ = lean_apply_2(v_toPure_2109_, lean_box(0), v___x_2118_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2120_, lean_object* v_st_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2120_, v_st_2121_);
lean_dec_ref(v_st_2121_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2123_, lean_object* v_t_2124_){
_start:
{
lean_object* v_toApplicative_2125_; lean_object* v_toBind_2126_; lean_object* v_get_2127_; lean_object* v_toPure_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; 
v_toApplicative_2125_ = lean_ctor_get(v_inst_2123_, 0);
lean_inc_ref(v_toApplicative_2125_);
v_toBind_2126_ = lean_ctor_get(v_inst_2123_, 1);
lean_inc(v_toBind_2126_);
lean_dec_ref(v_inst_2123_);
v_get_2127_ = lean_ctor_get(v_t_2124_, 0);
lean_inc(v_get_2127_);
lean_dec_ref(v_t_2124_);
v_toPure_2128_ = lean_ctor_get(v_toApplicative_2125_, 1);
lean_inc(v_toPure_2128_);
lean_dec_ref(v_toApplicative_2125_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2129_, 0, v_toPure_2128_);
v___x_2130_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v_get_2127_, v___f_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2131_, lean_object* v_inst_2132_, lean_object* v_t_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2132_, v_t_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2135_, lean_object* v_i_2136_){
_start:
{
lean_object* v_args_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_args_2137_ = lean_ctor_get(v_n_2135_, 2);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_array_get_borrowed(v___x_2138_, v_args_2137_, v_i_2136_);
v___x_2140_ = l_Lean_Syntax_getId(v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2141_, lean_object* v_i_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_SyntaxNode_getIdAt(v_n_2141_, v_i_2142_);
lean_dec(v_i_2142_);
lean_dec(v_n_2141_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2144_){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2146_ = lean_box(2);
v___x_2147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v_args_2144_);
return v___x_2147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 1)
{
lean_object* v_kind_2154_; 
v_kind_2154_ = lean_ctor_get(v_x_2153_, 1);
if (lean_obj_tag(v_kind_2154_) == 1)
{
lean_object* v_pre_2155_; lean_object* v_str_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_pre_2155_ = lean_ctor_get(v_kind_2154_, 0);
v_str_2156_ = lean_ctor_get(v_kind_2154_, 1);
v___x_2157_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2158_ = lean_string_dec_eq(v_str_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2160_ = lean_string_dec_eq(v_str_2156_, v___x_2159_);
if (v___x_2160_ == 0)
{
return v___x_2160_;
}
else
{
if (lean_obj_tag(v_pre_2155_) == 1)
{
lean_object* v_pre_2161_; 
v_pre_2161_ = lean_ctor_get(v_pre_2155_, 0);
if (lean_obj_tag(v_pre_2161_) == 1)
{
lean_object* v_pre_2162_; 
v_pre_2162_ = lean_ctor_get(v_pre_2161_, 0);
if (lean_obj_tag(v_pre_2162_) == 1)
{
lean_object* v_pre_2163_; 
v_pre_2163_ = lean_ctor_get(v_pre_2162_, 0);
if (lean_obj_tag(v_pre_2163_) == 0)
{
lean_object* v_str_2164_; lean_object* v_str_2165_; lean_object* v_str_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_str_2164_ = lean_ctor_get(v_pre_2155_, 1);
v_str_2165_ = lean_ctor_get(v_pre_2161_, 1);
v_str_2166_ = lean_ctor_get(v_pre_2162_, 1);
v___x_2167_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2168_ = lean_string_dec_eq(v_str_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2170_ = lean_string_dec_eq(v_str_2165_, v___x_2169_);
if (v___x_2170_ == 0)
{
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2172_ = lean_string_dec_eq(v_str_2164_, v___x_2171_);
return v___x_2172_;
}
}
}
else
{
return v___x_2158_;
}
}
else
{
return v___x_2158_;
}
}
else
{
return v___x_2158_;
}
}
else
{
return v___x_2158_;
}
}
}
else
{
return v___x_2158_;
}
}
else
{
uint8_t v___x_2173_; 
v___x_2173_ = 0;
return v___x_2173_;
}
}
else
{
uint8_t v___x_2174_; 
v___x_2174_ = 0;
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2175_){
_start:
{
uint8_t v_res_2176_; lean_object* v_r_2177_; 
v_res_2176_ = l_Lean_Syntax_isQuot(v_x_2175_);
lean_dec(v_x_2175_);
v_r_2177_ = lean_box(v_res_2176_);
return v_r_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2183_){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___y_2187_; uint8_t v___x_2193_; 
v___x_2184_ = l_Lean_Syntax_getNumArgs(v_stx_2183_);
v___x_2185_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_dec_eq(v___x_2184_, v___x_2185_);
lean_dec(v___x_2184_);
if (v___x_2193_ == 0)
{
v___y_2187_ = v_stx_2183_;
goto v___jp_2186_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = l_Lean_Syntax_getArg(v_stx_2183_, v___x_2194_);
lean_dec(v_stx_2183_);
v___y_2187_ = v___x_2195_;
goto v___jp_2186_;
}
v___jp_2186_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2187_);
v___x_2189_ = l_Lean_Syntax_isOfKind(v___y_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Syntax_getArg(v___y_2187_, v___x_2185_);
lean_dec(v___y_2187_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_unsigned_to_nat(3u);
v___x_2192_ = l_Lean_Syntax_getArg(v___y_2187_, v___x_2191_);
lean_dec(v___y_2187_);
return v___x_2192_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 1)
{
lean_object* v_kind_2198_; 
v_kind_2198_ = lean_ctor_get(v_x_2197_, 1);
if (lean_obj_tag(v_kind_2198_) == 1)
{
lean_object* v_str_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_str_2199_ = lean_ctor_get(v_kind_2198_, 1);
v___x_2200_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2201_ = lean_string_dec_eq(v_str_2199_, v___x_2200_);
return v___x_2201_;
}
else
{
uint8_t v___x_2202_; 
v___x_2202_ = 0;
return v___x_2202_;
}
}
else
{
uint8_t v___x_2203_; 
v___x_2203_ = 0;
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2204_){
_start:
{
uint8_t v_res_2205_; lean_object* v_r_2206_; 
v_res_2205_ = l_Lean_Syntax_isAntiquot(v_x_2204_);
lean_dec(v_x_2204_);
v_r_2206_ = lean_box(v_res_2205_);
return v_r_2206_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2207_, uint8_t v___x_2208_, lean_object* v_as_2209_, size_t v_i_2210_, size_t v_stop_2211_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_usize_dec_eq(v_i_2210_, v_stop_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; uint8_t v___y_2215_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2213_ = 1;
v___x_2219_ = lean_array_uget_borrowed(v_as_2209_, v_i_2210_);
v___x_2220_ = l_Lean_Syntax_isAntiquot(v___x_2219_);
if (v___x_2220_ == 0)
{
v___y_2215_ = v___y_2207_;
goto v___jp_2214_;
}
else
{
v___y_2215_ = v___x_2208_;
goto v___jp_2214_;
}
v___jp_2214_:
{
if (v___y_2215_ == 0)
{
size_t v___x_2216_; size_t v___x_2217_; 
v___x_2216_ = ((size_t)1ULL);
v___x_2217_ = lean_usize_add(v_i_2210_, v___x_2216_);
v_i_2210_ = v___x_2217_;
goto _start;
}
else
{
return v___x_2213_;
}
}
}
else
{
uint8_t v___x_2221_; 
v___x_2221_ = 0;
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2222_, lean_object* v___x_2223_, lean_object* v_as_2224_, lean_object* v_i_2225_, lean_object* v_stop_2226_){
_start:
{
uint8_t v___y_340__boxed_2227_; uint8_t v___x_341__boxed_2228_; size_t v_i_boxed_2229_; size_t v_stop_boxed_2230_; uint8_t v_res_2231_; lean_object* v_r_2232_; 
v___y_340__boxed_2227_ = lean_unbox(v___y_2222_);
v___x_341__boxed_2228_ = lean_unbox(v___x_2223_);
v_i_boxed_2229_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_stop_boxed_2230_ = lean_unbox_usize(v_stop_2226_);
lean_dec(v_stop_2226_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_340__boxed_2227_, v___x_341__boxed_2228_, v_as_2224_, v_i_boxed_2229_, v_stop_boxed_2230_);
lean_dec_ref(v_as_2224_);
v_r_2232_ = lean_box(v_res_2231_);
return v_r_2232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2233_){
_start:
{
uint8_t v___x_2234_; uint8_t v___y_2236_; 
v___x_2234_ = l_Lean_Syntax_isAntiquot(v_stx_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2233_);
v___x_2245_ = l_Lean_Syntax_isOfKind(v_stx_2233_, v___x_2244_);
if (v___x_2245_ == 0)
{
v___y_2236_ = v___x_2245_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = l_Lean_Syntax_getNumArgs(v_stx_2233_);
v___x_2248_ = lean_nat_dec_lt(v___x_2246_, v___x_2247_);
lean_dec(v___x_2247_);
v___y_2236_ = v___x_2248_;
goto v___jp_2235_;
}
}
else
{
lean_dec(v_stx_2233_);
return v___x_2234_;
}
v___jp_2235_:
{
if (v___y_2236_ == 0)
{
lean_dec(v_stx_2233_);
return v___y_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2237_ = l_Lean_Syntax_getArgs(v_stx_2233_);
lean_dec(v_stx_2233_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_array_get_size(v___x_2237_);
v___x_2240_ = lean_nat_dec_lt(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_dec_ref(v___x_2237_);
return v___y_2236_;
}
else
{
if (v___x_2240_ == 0)
{
lean_dec_ref(v___x_2237_);
return v___y_2236_;
}
else
{
size_t v___x_2241_; size_t v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = ((size_t)0ULL);
v___x_2242_ = lean_usize_of_nat(v___x_2239_);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2236_, v___x_2234_, v___x_2237_, v___x_2241_, v___x_2242_);
lean_dec_ref(v___x_2237_);
if (v___x_2243_ == 0)
{
return v___y_2236_;
}
else
{
return v___x_2234_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2249_){
_start:
{
uint8_t v_res_2250_; lean_object* v_r_2251_; 
v_res_2250_ = l_Lean_Syntax_isAntiquots(v_stx_2249_);
v_r_2251_ = lean_box(v_res_2250_);
return v_r_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2252_){
_start:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2252_);
v___x_2254_ = l_Lean_Syntax_isOfKind(v_stx_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
return v_stx_2252_;
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = l_Lean_Syntax_getArg(v_stx_2252_, v___x_2255_);
lean_dec(v_stx_2252_);
return v___x_2256_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2259_ = l_Lean_mkAtom(v___x_2258_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2263_ = lean_unsigned_to_nat(4u);
v___x_2264_ = lean_mk_empty_array_with_capacity(v___x_2263_);
v___x_2265_ = lean_array_push(v___x_2264_, v___x_2262_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2274_ = l_Lean_mkAtom(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2275_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2276_ = lean_unsigned_to_nat(2u);
v___x_2277_ = lean_mk_empty_array_with_capacity(v___x_2276_);
v___x_2278_ = lean_array_push(v___x_2277_, v___x_2275_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2290_ = l_Lean_mkAtom(v___x_2289_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2293_ = l_Lean_mkAtom(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2294_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2295_ = lean_unsigned_to_nat(3u);
v___x_2296_ = lean_mk_empty_array_with_capacity(v___x_2295_);
v___x_2297_ = lean_array_push(v___x_2296_, v___x_2294_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2298_, lean_object* v_term_2299_, lean_object* v_nesting_2300_, lean_object* v_name_2301_, uint8_t v_isPseudoKind_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_nesting_2307_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2326_; uint8_t v___x_2334_; 
v___x_2303_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2304_ = lean_mk_array(v_nesting_2300_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2306_ = lean_box(2);
v_nesting_2307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2307_, 0, v___x_2306_);
lean_ctor_set(v_nesting_2307_, 1, v___x_2305_);
lean_ctor_set(v_nesting_2307_, 2, v___x_2304_);
v___x_2334_ = l_Lean_Syntax_isIdent(v_term_2299_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2299_);
v___x_2336_ = l_Lean_Syntax_isOfKind(v_term_2299_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2337_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2338_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2339_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2340_ = lean_array_push(v___x_2339_, v_term_2299_);
v___x_2341_ = lean_array_push(v___x_2340_, v___x_2338_);
v___x_2342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2306_);
lean_ctor_set(v___x_2342_, 1, v___x_2337_);
lean_ctor_set(v___x_2342_, 2, v___x_2341_);
v___y_2326_ = v___x_2342_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = l_Lean_Syntax_getArg(v_term_2299_, v___x_2343_);
lean_dec(v_term_2299_);
v___y_2326_ = v___x_2344_;
goto v___jp_2325_;
}
}
else
{
v___y_2326_ = v_term_2299_;
goto v___jp_2325_;
}
v___jp_2308_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_inc(v___y_2311_);
v___x_2312_ = l_Lean_Name_append(v_kind_2298_, v___y_2311_);
v___x_2313_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2314_ = l_Lean_Name_append(v___x_2312_, v___x_2313_);
v___x_2315_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2316_ = lean_array_push(v___x_2315_, v_nesting_2307_);
v___x_2317_ = lean_array_push(v___x_2316_, v___y_2309_);
v___x_2318_ = lean_array_push(v___x_2317_, v___y_2310_);
v___x_2319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2306_);
lean_ctor_set(v___x_2319_, 1, v___x_2314_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
return v___x_2319_;
}
v___jp_2320_:
{
if (v_isPseudoKind_2302_ == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_box(0);
v___y_2309_ = v___y_2321_;
v___y_2310_ = v___y_2322_;
v___y_2311_ = v___x_2323_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2324_; 
v___x_2324_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2309_ = v___y_2321_;
v___y_2310_ = v___y_2322_;
v___y_2311_ = v___x_2324_;
goto v___jp_2308_;
}
}
v___jp_2325_:
{
if (lean_obj_tag(v_name_2301_) == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2321_ = v___y_2326_;
v___y_2322_ = v___x_2327_;
goto v___jp_2320_;
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_val_2328_ = lean_ctor_get(v_name_2301_, 0);
lean_inc(v_val_2328_);
lean_dec_ref(v_name_2301_);
v___x_2329_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2330_ = l_Lean_mkAtom(v_val_2328_);
v___x_2331_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2332_ = lean_array_push(v___x_2331_, v___x_2330_);
v___x_2333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2306_);
lean_ctor_set(v___x_2333_, 1, v___x_2329_);
lean_ctor_set(v___x_2333_, 2, v___x_2332_);
v___y_2321_ = v___y_2326_;
v___y_2322_ = v___x_2333_;
goto v___jp_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2345_, lean_object* v_term_2346_, lean_object* v_nesting_2347_, lean_object* v_name_2348_, lean_object* v_isPseudoKind_2349_){
_start:
{
uint8_t v_isPseudoKind_boxed_2350_; lean_object* v_res_2351_; 
v_isPseudoKind_boxed_2350_ = lean_unbox(v_isPseudoKind_2349_);
v_res_2351_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2345_, v_term_2346_, v_nesting_2347_, v_name_2348_, v_isPseudoKind_boxed_2350_);
return v_res_2351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2352_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = l_Lean_Syntax_getArg(v_stx_2352_, v___x_2353_);
v___x_2355_ = l_Lean_Syntax_getArgs(v___x_2354_);
lean_dec(v___x_2354_);
v___x_2356_ = lean_array_get_size(v___x_2355_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = lean_unsigned_to_nat(0u);
v___x_2358_ = lean_nat_dec_eq(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
uint8_t v___x_2359_; 
v___x_2359_ = 1;
return v___x_2359_;
}
else
{
uint8_t v___x_2360_; 
v___x_2360_ = 0;
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2361_){
_start:
{
uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_res_2362_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2361_);
lean_dec(v_stx_2361_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_Lean_Syntax_isAntiquot(v_stx_2364_);
if (v___x_2365_ == 0)
{
return v_stx_2364_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_getArgs(v___x_2367_);
lean_dec(v___x_2367_);
v___x_2369_ = lean_array_pop(v___x_2368_);
v___x_2370_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2371_ = lean_box(2);
v___x_2372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v___x_2370_);
lean_ctor_set(v___x_2372_, 2, v___x_2369_);
v___x_2373_ = l_Lean_Syntax_setArg(v_stx_2364_, v___x_2366_, v___x_2372_);
return v___x_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2374_){
_start:
{
lean_object* v___y_2376_; uint8_t v___x_2387_; 
v___x_2387_ = l_Lean_Syntax_isAntiquot(v_stx_2374_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_unsigned_to_nat(3u);
v___x_2389_ = l_Lean_Syntax_getArg(v_stx_2374_, v___x_2388_);
v___y_2376_ = v___x_2389_;
goto v___jp_2375_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(2u);
v___x_2391_ = l_Lean_Syntax_getArg(v_stx_2374_, v___x_2390_);
v___y_2376_ = v___x_2391_;
goto v___jp_2375_;
}
v___jp_2375_:
{
uint8_t v___x_2377_; 
v___x_2377_ = l_Lean_Syntax_isIdent(v___y_2376_);
if (v___x_2377_ == 0)
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_Syntax_isAtom(v___y_2376_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = l_Lean_Syntax_getArg(v___y_2376_, v___x_2379_);
lean_dec(v___y_2376_);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2381_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2382_ = lean_unsigned_to_nat(1u);
v___x_2383_ = lean_mk_empty_array_with_capacity(v___x_2382_);
v___x_2384_ = lean_array_push(v___x_2383_, v___y_2376_);
v___x_2385_ = lean_box(2);
v___x_2386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___x_2381_);
lean_ctor_set(v___x_2386_, 2, v___x_2384_);
return v___x_2386_;
}
}
else
{
return v___y_2376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2392_);
lean_dec(v_stx_2392_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2394_){
_start:
{
if (lean_obj_tag(v_x_2394_) == 1)
{
lean_object* v_kind_2395_; 
v_kind_2395_ = lean_ctor_get(v_x_2394_, 1);
if (lean_obj_tag(v_kind_2395_) == 1)
{
lean_object* v_pre_2396_; lean_object* v_str_2397_; 
v_pre_2396_ = lean_ctor_get(v_kind_2395_, 0);
v_str_2397_ = lean_ctor_get(v_kind_2395_, 1);
if (lean_obj_tag(v_pre_2396_) == 1)
{
lean_object* v_pre_2403_; lean_object* v_str_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_pre_2403_ = lean_ctor_get(v_pre_2396_, 0);
v_str_2404_ = lean_ctor_get(v_pre_2396_, 1);
v___x_2405_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2406_ = lean_string_dec_eq(v_str_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2408_ = lean_string_dec_eq(v_str_2397_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_box(0);
return v___x_2409_;
}
else
{
goto v___jp_2398_;
}
}
else
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2411_ = lean_string_dec_eq(v_str_2397_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_box(0);
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = lean_box(v___x_2411_);
lean_inc(v_pre_2403_);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v_pre_2403_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
}
else
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2417_ = lean_string_dec_eq(v_str_2397_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_box(0);
return v___x_2418_;
}
else
{
goto v___jp_2398_;
}
}
v___jp_2398_:
{
uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2399_ = 0;
v___x_2400_ = lean_box(v___x_2399_);
lean_inc(v_pre_2396_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_pre_2396_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_box(0);
return v___x_2419_;
}
}
else
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_box(0);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2421_);
lean_dec(v_x_2421_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2423_, size_t v_i_2424_, size_t v_stop_2425_, lean_object* v_b_2426_){
_start:
{
lean_object* v___y_2428_; uint8_t v___x_2432_; 
v___x_2432_ = lean_usize_dec_eq(v_i_2424_, v_stop_2425_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_array_uget_borrowed(v_as_2423_, v_i_2424_);
v___x_2434_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2433_);
if (lean_obj_tag(v___x_2434_) == 0)
{
v___y_2428_ = v_b_2426_;
goto v___jp_2427_;
}
else
{
lean_object* v_val_2435_; lean_object* v___x_2436_; 
v_val_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_val_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = lean_array_push(v_b_2426_, v_val_2435_);
v___y_2428_ = v___x_2436_;
goto v___jp_2427_;
}
}
else
{
return v_b_2426_;
}
v___jp_2427_:
{
size_t v___x_2429_; size_t v___x_2430_; 
v___x_2429_ = ((size_t)1ULL);
v___x_2430_ = lean_usize_add(v_i_2424_, v___x_2429_);
v_i_2424_ = v___x_2430_;
v_b_2426_ = v___y_2428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2437_, lean_object* v_i_2438_, lean_object* v_stop_2439_, lean_object* v_b_2440_){
_start:
{
size_t v_i_boxed_2441_; size_t v_stop_boxed_2442_; lean_object* v_res_2443_; 
v_i_boxed_2441_ = lean_unbox_usize(v_i_2438_);
lean_dec(v_i_2438_);
v_stop_boxed_2442_ = lean_unbox_usize(v_stop_2439_);
lean_dec(v_stop_2439_);
v_res_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2437_, v_i_boxed_2441_, v_stop_boxed_2442_, v_b_2440_);
lean_dec_ref(v_as_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2446_, lean_object* v_start_2447_, lean_object* v_stop_2448_){
_start:
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2450_ = lean_nat_dec_lt(v_start_2447_, v_stop_2448_);
if (v___x_2450_ == 0)
{
return v___x_2449_;
}
else
{
lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = lean_array_get_size(v_as_2446_);
v___x_2452_ = lean_nat_dec_le(v_stop_2448_, v___x_2451_);
if (v___x_2452_ == 0)
{
uint8_t v___x_2453_; 
v___x_2453_ = lean_nat_dec_lt(v_start_2447_, v___x_2451_);
if (v___x_2453_ == 0)
{
return v___x_2449_;
}
else
{
size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = lean_usize_of_nat(v_start_2447_);
v___x_2455_ = lean_usize_of_nat(v___x_2451_);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2446_, v___x_2454_, v___x_2455_, v___x_2449_);
return v___x_2456_;
}
}
else
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = lean_usize_of_nat(v_start_2447_);
v___x_2458_ = lean_usize_of_nat(v_stop_2448_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2446_, v___x_2457_, v___x_2458_, v___x_2449_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2460_, lean_object* v_start_2461_, lean_object* v_stop_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2460_, v_start_2461_, v_stop_2462_);
lean_dec(v_stop_2462_);
lean_dec(v_start_2461_);
lean_dec_ref(v_as_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2464_){
_start:
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2464_);
v___x_2466_ = l_Lean_Syntax_isOfKind(v_stx_2464_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2464_);
lean_dec(v_stx_2464_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_box(0);
return v___x_2468_;
}
else
{
lean_object* v_val_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_val_2469_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2469_);
lean_dec_ref(v___x_2467_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_val_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
return v___x_2471_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2472_ = l_Lean_Syntax_getArgs(v_stx_2464_);
lean_dec(v_stx_2464_);
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = lean_array_get_size(v___x_2472_);
v___x_2475_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2472_, v___x_2473_, v___x_2474_);
lean_dec_ref(v___x_2472_);
v___x_2476_ = lean_array_to_list(v___x_2475_);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2478_){
_start:
{
if (lean_obj_tag(v_x_2478_) == 1)
{
lean_object* v_kind_2479_; 
v_kind_2479_ = lean_ctor_get(v_x_2478_, 1);
if (lean_obj_tag(v_kind_2479_) == 1)
{
lean_object* v_pre_2480_; lean_object* v_str_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_pre_2480_ = lean_ctor_get(v_kind_2479_, 0);
v_str_2481_ = lean_ctor_get(v_kind_2479_, 1);
v___x_2482_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2483_ = lean_string_dec_eq(v_str_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
lean_inc(v_pre_2480_);
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_pre_2480_);
return v___x_2485_;
}
}
else
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_box(0);
return v___x_2486_;
}
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_box(0);
return v___x_2487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2488_);
lean_dec(v_x_2488_);
return v_res_2489_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
uint8_t v___x_2492_; 
v___x_2492_ = 0;
return v___x_2492_;
}
else
{
uint8_t v___x_2493_; 
lean_dec_ref(v___x_2491_);
v___x_2493_ = 1;
return v___x_2493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2494_);
lean_dec(v_stx_2494_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_unsigned_to_nat(3u);
v___x_2499_ = l_Lean_Syntax_getArg(v_stx_2497_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_getArgs(v___x_2499_);
lean_dec(v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2501_);
lean_dec(v_stx_2501_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2503_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_unsigned_to_nat(1u);
v___x_2506_ = l_Lean_Syntax_getArg(v_stx_2503_, v___x_2505_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_unsigned_to_nat(5u);
v___x_2508_ = l_Lean_Syntax_getArg(v_stx_2503_, v___x_2507_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2509_);
lean_dec(v_stx_2509_);
return v_res_2510_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2516_ = l_Lean_mkAtom(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2519_ = l_Lean_mkAtom(v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2520_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2521_ = lean_unsigned_to_nat(6u);
v___x_2522_ = lean_mk_empty_array_with_capacity(v___x_2521_);
v___x_2523_ = lean_array_push(v___x_2522_, v___x_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2524_, lean_object* v_contents_2525_, lean_object* v_suffix_2526_, lean_object* v_nesting_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_nesting_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2528_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2529_ = lean_mk_array(v_nesting_2527_, v___x_2528_);
v___x_2530_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2531_ = lean_box(2);
v_nesting_2532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2532_, 0, v___x_2531_);
lean_ctor_set(v_nesting_2532_, 1, v___x_2530_);
lean_ctor_set(v_nesting_2532_, 2, v___x_2529_);
v___x_2533_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2534_ = l_Lean_Name_append(v_kind_2524_, v___x_2533_);
v___x_2535_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2531_);
lean_ctor_set(v___x_2536_, 1, v___x_2530_);
lean_ctor_set(v___x_2536_, 2, v_contents_2525_);
v___x_2537_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2538_ = l_Lean_mkAtom(v_suffix_2526_);
v___x_2539_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2540_ = lean_array_push(v___x_2539_, v_nesting_2532_);
v___x_2541_ = lean_array_push(v___x_2540_, v___x_2535_);
v___x_2542_ = lean_array_push(v___x_2541_, v___x_2536_);
v___x_2543_ = lean_array_push(v___x_2542_, v___x_2537_);
v___x_2544_ = lean_array_push(v___x_2543_, v___x_2538_);
v___x_2545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2531_);
lean_ctor_set(v___x_2545_, 1, v___x_2534_);
lean_ctor_set(v___x_2545_, 2, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2547_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 1)
{
lean_object* v_kind_2548_; 
v_kind_2548_ = lean_ctor_get(v_x_2547_, 1);
if (lean_obj_tag(v_kind_2548_) == 1)
{
lean_object* v_pre_2549_; lean_object* v_str_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v_pre_2549_ = lean_ctor_get(v_kind_2548_, 0);
v_str_2550_ = lean_ctor_get(v_kind_2548_, 1);
v___x_2551_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2552_ = lean_string_dec_eq(v_str_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_box(0);
return v___x_2553_;
}
else
{
lean_object* v___x_2554_; 
lean_inc(v_pre_2549_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_pre_2549_);
return v___x_2554_;
}
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_box(0);
return v___x_2555_;
}
}
else
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_box(0);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2557_);
lean_dec(v_x_2557_);
return v_res_2558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
uint8_t v___x_2561_; 
v___x_2561_ = 0;
return v___x_2561_;
}
else
{
uint8_t v___x_2562_; 
lean_dec_ref(v___x_2560_);
v___x_2562_ = 1;
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2563_){
_start:
{
uint8_t v_res_2564_; lean_object* v_r_2565_; 
v_res_2564_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2563_);
lean_dec(v_stx_2563_);
v_r_2565_ = lean_box(v_res_2564_);
return v_r_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = l_Lean_Syntax_getArg(v_stx_2566_, v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2569_);
lean_dec(v_stx_2569_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2573_, lean_object* v_inner_2574_, lean_object* v_suffix_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2576_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2577_ = l_Lean_Name_append(v_kind_2573_, v___x_2576_);
v___x_2578_ = l_Lean_mkAtom(v_suffix_2575_);
v___x_2579_ = lean_unsigned_to_nat(2u);
v___x_2580_ = lean_mk_empty_array_with_capacity(v___x_2579_);
v___x_2581_ = lean_array_push(v___x_2580_, v_inner_2574_);
v___x_2582_ = lean_array_push(v___x_2581_, v___x_2578_);
v___x_2583_ = lean_box(2);
v___x_2584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2577_);
lean_ctor_set(v___x_2584_, 2, v___x_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2588_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2590_ = l_Lean_Syntax_isOfKind(v_stx_2588_, v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2591_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2594_){
_start:
{
uint8_t v___y_2596_; uint8_t v___x_2599_; 
v___x_2599_ = l_Lean_Syntax_isAntiquot(v_stx_2594_);
if (v___x_2599_ == 0)
{
uint8_t v___x_2600_; 
v___x_2600_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2594_);
v___y_2596_ = v___x_2600_;
goto v___jp_2595_;
}
else
{
v___y_2596_ = v___x_2599_;
goto v___jp_2595_;
}
v___jp_2595_:
{
if (v___y_2596_ == 0)
{
uint8_t v___x_2597_; 
v___x_2597_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2594_);
if (v___x_2597_ == 0)
{
uint8_t v___x_2598_; 
v___x_2598_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2594_);
return v___x_2598_;
}
else
{
lean_dec(v_stx_2594_);
return v___x_2597_;
}
}
else
{
lean_dec(v_stx_2594_);
return v___y_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2601_){
_start:
{
uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_res_2602_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2601_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2607_, lean_object* v_stx_2608_, lean_object* v_visit_2609_, lean_object* v_stack_2610_, lean_object* v_accept_2611_, lean_object* v_a_2612_, lean_object* v_b_2613_){
_start:
{
lean_object* v_a_2615_; uint8_t v___x_2619_; 
v___x_2619_ = lean_nat_dec_lt(v_a_2612_, v_upperBound_2607_);
if (v___x_2619_ == 0)
{
lean_dec(v_a_2612_);
lean_dec_ref(v_accept_2611_);
lean_dec(v_stack_2610_);
lean_dec_ref(v_visit_2609_);
lean_dec(v_stx_2608_);
lean_inc_ref(v_b_2613_);
return v_b_2613_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2620_ = lean_box(0);
v___x_2621_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2622_ = l_Lean_Syntax_getArg(v_stx_2608_, v_a_2612_);
lean_inc_ref(v_visit_2609_);
lean_inc(v___x_2622_);
v___x_2623_ = lean_apply_1(v_visit_2609_, v___x_2622_);
v___x_2624_ = lean_unbox(v___x_2623_);
if (v___x_2624_ == 0)
{
lean_dec(v___x_2622_);
v_a_2615_ = v___x_2621_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_inc(v_a_2612_);
lean_inc(v_stx_2608_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_stx_2608_);
lean_ctor_set(v___x_2625_, 1, v_a_2612_);
lean_inc(v_stack_2610_);
v___x_2626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v_stack_2610_);
lean_inc_ref(v_accept_2611_);
lean_inc_ref(v_visit_2609_);
v___x_2627_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2609_, v_accept_2611_, v___x_2626_, v___x_2622_);
if (lean_obj_tag(v___x_2627_) == 1)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec(v_a_2612_);
lean_dec_ref(v_accept_2611_);
lean_dec(v_stack_2610_);
lean_dec_ref(v_visit_2609_);
lean_dec(v_stx_2608_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v___x_2620_);
return v___x_2629_;
}
else
{
lean_dec(v___x_2627_);
v_a_2615_ = v___x_2621_;
goto v___jp_2614_;
}
}
}
v___jp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_a_2612_, v___x_2616_);
lean_dec(v_a_2612_);
v_a_2612_ = v___x_2617_;
v_b_2613_ = v_a_2615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2630_, lean_object* v_accept_2631_, lean_object* v_stack_2632_, lean_object* v_stx_2633_){
_start:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
lean_inc_ref(v_accept_2631_);
lean_inc(v_stx_2633_);
v___x_2634_ = lean_apply_1(v_accept_2631_, v_stx_2633_);
v___x_2635_ = lean_unbox(v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_fst_2641_; 
v___x_2636_ = l_Lean_Syntax_getNumArgs(v_stx_2633_);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_box(0);
v___x_2639_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2636_, v_stx_2633_, v_visit_2630_, v_stack_2632_, v_accept_2631_, v___x_2637_, v___x_2639_);
lean_dec(v___x_2636_);
v_fst_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_fst_2641_);
lean_dec_ref(v___x_2640_);
if (lean_obj_tag(v_fst_2641_) == 0)
{
return v___x_2638_;
}
else
{
lean_object* v_val_2642_; 
v_val_2642_ = lean_ctor_get(v_fst_2641_, 0);
lean_inc(v_val_2642_);
lean_dec_ref(v_fst_2641_);
return v_val_2642_;
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec_ref(v_accept_2631_);
lean_dec_ref(v_visit_2630_);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_stx_2633_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v_stack_2632_);
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2647_, lean_object* v_stx_2648_, lean_object* v_visit_2649_, lean_object* v_stack_2650_, lean_object* v_accept_2651_, lean_object* v_a_2652_, lean_object* v_b_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2647_, v_stx_2648_, v_visit_2649_, v_stack_2650_, v_accept_2651_, v_a_2652_, v_b_2653_);
lean_dec_ref(v_b_2653_);
lean_dec(v_upperBound_2647_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2655_, lean_object* v_stx_2656_, lean_object* v_visit_2657_, lean_object* v_stack_2658_, lean_object* v_accept_2659_, lean_object* v_inst_2660_, lean_object* v_R_2661_, lean_object* v_a_2662_, lean_object* v_b_2663_, lean_object* v_c_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2655_, v_stx_2656_, v_visit_2657_, v_stack_2658_, v_accept_2659_, v_a_2662_, v_b_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2666_, lean_object* v_stx_2667_, lean_object* v_visit_2668_, lean_object* v_stack_2669_, lean_object* v_accept_2670_, lean_object* v_inst_2671_, lean_object* v_R_2672_, lean_object* v_a_2673_, lean_object* v_b_2674_, lean_object* v_c_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2666_, v_stx_2667_, v_visit_2668_, v_stack_2669_, v_accept_2670_, v_inst_2671_, v_R_2672_, v_a_2673_, v_b_2674_, v_c_2675_);
lean_dec_ref(v_b_2674_);
lean_dec(v_upperBound_2666_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2677_, lean_object* v_visit_2678_, lean_object* v_accept_2679_){
_start:
{
lean_object* v___x_2680_; uint8_t v___x_2681_; 
lean_inc_ref(v_visit_2678_);
lean_inc(v_root_2677_);
v___x_2680_ = lean_apply_1(v_visit_2678_, v_root_2677_);
v___x_2681_ = lean_unbox(v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
lean_dec_ref(v_accept_2679_);
lean_dec_ref(v_visit_2678_);
lean_dec(v_root_2677_);
v___x_2682_ = lean_box(0);
return v___x_2682_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_box(0);
v___x_2684_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2678_, v_accept_2679_, v___x_2683_, v_root_2677_);
return v___x_2684_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___y_2685_){
_start:
{
return v___y_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___y_2686_){
_start:
{
uint8_t v___y_107__boxed_2687_; uint8_t v_res_2688_; lean_object* v_r_2689_; 
v___y_107__boxed_2687_ = lean_unbox(v___y_2686_);
v_res_2688_ = l_Lean_Syntax_Stack_matches___lam__0(v___y_107__boxed_2687_);
v_r_2689_ = lean_box(v_res_2688_);
return v_r_2689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__1(uint8_t v___x_2690_, lean_object* v_x_2691_, lean_object* v_p_2692_){
_start:
{
if (lean_obj_tag(v_p_2692_) == 0)
{
lean_dec_ref(v_x_2691_);
return v___x_2690_;
}
else
{
lean_object* v_fst_2693_; lean_object* v_val_2694_; uint8_t v___x_2695_; 
v_fst_2693_ = lean_ctor_get(v_x_2691_, 0);
lean_inc(v_fst_2693_);
lean_dec_ref(v_x_2691_);
v_val_2694_ = lean_ctor_get(v_p_2692_, 0);
v___x_2695_ = l_Lean_Syntax_isOfKind(v_fst_2693_, v_val_2694_);
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__1___boxed(lean_object* v___x_2696_, lean_object* v_x_2697_, lean_object* v_p_2698_){
_start:
{
uint8_t v___x_110__boxed_2699_; uint8_t v_res_2700_; lean_object* v_r_2701_; 
v___x_110__boxed_2699_ = lean_unbox(v___x_2696_);
v_res_2700_ = l_Lean_Syntax_Stack_matches___lam__1(v___x_110__boxed_2699_, v_x_2697_, v_p_2698_);
lean_dec(v_p_2698_);
v_r_2701_ = lean_box(v_res_2700_);
return v_r_2701_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2705_, lean_object* v_pattern_2706_){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2707_ = l_List_lengthTR___redArg(v_pattern_2706_);
v___x_2708_ = l_List_lengthTR___redArg(v_stack_2705_);
v___x_2709_ = lean_nat_dec_le(v___x_2707_, v___x_2708_);
lean_dec(v___x_2708_);
lean_dec(v___x_2707_);
if (v___x_2709_ == 0)
{
lean_dec(v_pattern_2706_);
lean_dec(v_stack_2705_);
return v___x_2709_;
}
else
{
lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___f_2710_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2711_ = lean_box(v___x_2709_);
v___f_2712_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2712_, 0, v___x_2711_);
v___x_2713_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__1));
v___x_2714_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2712_, v_stack_2705_, v_pattern_2706_, v___x_2713_);
v___x_2715_ = l_List_all___redArg(v___x_2714_, v___f_2710_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2716_, lean_object* v_pattern_2717_){
_start:
{
uint8_t v_res_2718_; lean_object* v_r_2719_; 
v_res_2718_ = l_Lean_Syntax_Stack_matches(v_stack_2716_, v_pattern_2717_);
v_r_2719_ = lean_box(v_res_2718_);
return v_r_2719_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

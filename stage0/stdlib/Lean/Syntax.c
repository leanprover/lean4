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
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object*);
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
static const lean_array_object l_Lean_Syntax_identComponents_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__0_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__1_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.identComponents\?"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__2 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__2_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__3 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Syntax_identComponents_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_identComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Syntax.identComponents"};
static const lean_object* l_Lean_Syntax_identComponents___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_identComponents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents___closed__1;
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
lean_dec_ref_known(v_x_1126_, 2);
lean_dec(v_info_1132_);
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
lean_dec(v_info_1184_);
lean_dec_ref_known(v___y_1164_, 4);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
return v_x_1325_;
}
else
{
lean_object* v_head_1327_; lean_object* v_tail_1328_; lean_object* v___x_1329_; 
v_head_1327_ = lean_ctor_get(v_x_1326_, 0);
lean_inc(v_head_1327_);
v_tail_1328_ = lean_ctor_get(v_x_1326_, 1);
lean_inc(v_tail_1328_);
lean_dec_ref_known(v_x_1326_, 2);
v___x_1329_ = l_Lean_Name_append(v_x_1325_, v_head_1327_);
v_x_1325_ = v___x_1329_;
v_x_1326_ = v_tail_1328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1333_, lean_object* v_nFields_x3f_1334_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1334_) == 1)
{
lean_object* v_val_1335_; lean_object* v_nameComps_1336_; lean_object* v___x_1337_; lean_object* v_nPrefix_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_namePrefix_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_val_1335_ = lean_ctor_get(v_nFields_x3f_1334_, 0);
v_nameComps_1336_ = l_Lean_Name_components(v_n_1333_);
v___x_1337_ = l_List_lengthTR___redArg(v_nameComps_1336_);
v_nPrefix_1338_ = lean_nat_sub(v___x_1337_, v_val_1335_);
lean_dec(v___x_1337_);
v___x_1339_ = lean_box(0);
v___x_1340_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1338_);
lean_inc(v_nameComps_1336_);
v___x_1341_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1336_, v_nameComps_1336_, v_nPrefix_1338_, v___x_1340_);
v_namePrefix_1342_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1339_, v___x_1341_);
v___x_1343_ = l_List_drop___redArg(v_nPrefix_1338_, v_nameComps_1336_);
lean_dec(v_nameComps_1336_);
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_namePrefix_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Name_components(v_n_1333_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1346_, lean_object* v_nFields_x3f_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1346_, v_nFields_x3f_1347_);
lean_dec(v_nFields_x3f_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_panic_fn_borrowed(v___x_1350_, v_msg_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
if (lean_obj_tag(v_x_1353_) == 0)
{
return v_x_1352_;
}
else
{
lean_object* v_head_1354_; lean_object* v_tail_1355_; lean_object* v_startPos_1356_; lean_object* v_stopPos_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_head_1354_ = lean_ctor_get(v_x_1353_, 0);
v_tail_1355_ = lean_ctor_get(v_x_1353_, 1);
v_startPos_1356_ = lean_ctor_get(v_head_1354_, 1);
v_stopPos_1357_ = lean_ctor_get(v_head_1354_, 2);
v___x_1358_ = lean_nat_sub(v_stopPos_1357_, v_startPos_1356_);
v___x_1359_ = lean_nat_add(v_x_1352_, v___x_1358_);
lean_dec(v___x_1358_);
lean_dec(v_x_1352_);
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_nat_add(v___x_1359_, v___x_1360_);
lean_dec(v___x_1359_);
v_x_1352_ = v___x_1361_;
v_x_1353_ = v_tail_1355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1363_, v_x_1364_);
lean_dec(v_x_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1370_, lean_object* v_pos_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
if (lean_obj_tag(v_a_1372_) == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = l_List_reverse___redArg(v_a_1373_);
return v___x_1374_;
}
else
{
lean_object* v_head_1375_; lean_object* v_tail_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1394_; 
v_head_1375_ = lean_ctor_get(v_a_1372_, 0);
v_tail_1376_ = lean_ctor_get(v_a_1372_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_a_1372_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1378_ = v_a_1372_;
v_isShared_1379_ = v_isSharedCheck_1394_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_tail_1376_);
lean_inc(v_head_1375_);
lean_dec(v_a_1372_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1394_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_stopPos_1380_; lean_object* v_startPos_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_info_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v_stopPos_1380_ = lean_ctor_get(v_head_1375_, 2);
lean_inc(v_stopPos_1380_);
lean_dec(v_head_1375_);
v_startPos_1381_ = lean_ctor_get(v_rawVal_1370_, 1);
v___x_1382_ = lean_nat_sub(v_stopPos_1380_, v_startPos_1381_);
lean_dec(v_stopPos_1380_);
v___x_1383_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1384_ = lean_nat_add(v___x_1382_, v_pos_1371_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_add(v___x_1385_, v___x_1384_);
v_info_1387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1387_, 0, v___x_1383_);
lean_ctor_set(v_info_1387_, 1, v___x_1384_);
lean_ctor_set(v_info_1387_, 2, v___x_1383_);
lean_ctor_set(v_info_1387_, 3, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_info_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v_a_1373_);
lean_ctor_set(v___x_1378_, 0, v___x_1389_);
v___x_1391_ = v___x_1378_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_a_1373_);
v___x_1391_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v_a_1372_ = v_tail_1376_;
v_a_1373_ = v___x_1391_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1395_, lean_object* v_pos_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1395_, v_pos_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_pos_1396_);
lean_dec_ref(v_rawVal_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1400_, lean_object* v_pos_1401_, lean_object* v_trailing_1402_, lean_object* v_leading_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
if (lean_obj_tag(v_a_1404_) == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_leading_1403_);
lean_dec_ref(v_trailing_1402_);
v___x_1406_ = l_List_reverse___redArg(v_a_1405_);
return v___x_1406_;
}
else
{
lean_object* v_head_1407_; lean_object* v_snd_1408_; lean_object* v_tail_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1439_; 
v_head_1407_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_head_1407_);
v_snd_1408_ = lean_ctor_get(v_head_1407_, 1);
lean_inc(v_snd_1408_);
v_tail_1409_ = lean_ctor_get(v_a_1404_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1404_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_a_1404_, 0);
lean_dec(v_unused_1440_);
v___x_1411_ = v_a_1404_;
v_isShared_1412_ = v_isSharedCheck_1439_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_tail_1409_);
lean_dec(v_a_1404_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1439_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_fst_1413_; lean_object* v_startPos_1414_; lean_object* v_stopPos_1415_; lean_object* v_startPos_1416_; lean_object* v_stopPos_1417_; lean_object* v_off_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1433_; lean_object* v___x_1436_; uint8_t v_decide_1437_; 
v_fst_1413_ = lean_ctor_get(v_head_1407_, 0);
lean_inc(v_fst_1413_);
lean_dec(v_head_1407_);
v_startPos_1414_ = lean_ctor_get(v_snd_1408_, 1);
v_stopPos_1415_ = lean_ctor_get(v_snd_1408_, 2);
v_startPos_1416_ = lean_ctor_get(v_rawVal_1400_, 1);
v_stopPos_1417_ = lean_ctor_get(v_rawVal_1400_, 2);
v_off_1418_ = lean_nat_sub(v_startPos_1414_, v_startPos_1416_);
v___x_1436_ = lean_unsigned_to_nat(0u);
v_decide_1437_ = lean_nat_dec_eq(v_off_1418_, v___x_1436_);
if (v_decide_1437_ == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1433_ = v___x_1438_;
goto v___jp_1432_;
}
else
{
lean_inc_ref(v_leading_1403_);
v___y_1433_ = v_leading_1403_;
goto v___jp_1432_;
}
v___jp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_info_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1422_ = lean_nat_add(v_off_1418_, v_pos_1401_);
lean_dec(v_off_1418_);
v___x_1423_ = lean_nat_sub(v_stopPos_1415_, v_startPos_1414_);
v___x_1424_ = lean_nat_add(v___x_1423_, v___x_1422_);
lean_dec(v___x_1423_);
v_info_1425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1425_, 0, v___y_1420_);
lean_ctor_set(v_info_1425_, 1, v___x_1422_);
lean_ctor_set(v_info_1425_, 2, v___y_1421_);
lean_ctor_set(v_info_1425_, 3, v___x_1424_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1427_, 0, v_info_1425_);
lean_ctor_set(v___x_1427_, 1, v_snd_1408_);
lean_ctor_set(v___x_1427_, 2, v_fst_1413_);
lean_ctor_set(v___x_1427_, 3, v___x_1426_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v_a_1405_);
lean_ctor_set(v___x_1411_, 0, v___x_1427_);
v___x_1429_ = v___x_1411_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_a_1405_);
v___x_1429_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v_a_1404_ = v_tail_1409_;
v_a_1405_ = v___x_1429_;
goto _start;
}
}
v___jp_1432_:
{
uint8_t v_decide_1434_; 
v_decide_1434_ = lean_nat_dec_eq(v_stopPos_1415_, v_stopPos_1417_);
if (v_decide_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1420_ = v___y_1433_;
v___y_1421_ = v___x_1435_;
goto v___jp_1419_;
}
else
{
lean_inc_ref(v_trailing_1402_);
v___y_1420_ = v___y_1433_;
v___y_1421_ = v_trailing_1402_;
goto v___jp_1419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1441_, lean_object* v_pos_1442_, lean_object* v_trailing_1443_, lean_object* v_leading_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1441_, v_pos_1442_, v_trailing_1443_, v_leading_1444_, v_a_1445_, v_a_1446_);
lean_dec(v_pos_1442_);
lean_dec_ref(v_rawVal_1441_);
return v_res_1447_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__4(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1453_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1454_ = lean_unsigned_to_nat(9u);
v___x_1455_ = lean_unsigned_to_nat(358u);
v___x_1456_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1457_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1458_ = l_mkPanicMessageWithDecl(v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_, v___x_1453_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1459_, lean_object* v_nFields_x3f_1460_){
_start:
{
if (lean_obj_tag(v_stx_1459_) == 3)
{
lean_object* v_info_1461_; 
v_info_1461_ = lean_ctor_get(v_stx_1459_, 0);
lean_inc(v_info_1461_);
if (lean_obj_tag(v_info_1461_) == 0)
{
lean_object* v_rawVal_1462_; lean_object* v_val_1463_; lean_object* v_leading_1464_; lean_object* v_pos_1465_; lean_object* v_trailing_1466_; lean_object* v_rawComps_1467_; uint8_t v___x_1468_; 
v_rawVal_1462_ = lean_ctor_get(v_stx_1459_, 1);
lean_inc_ref_n(v_rawVal_1462_, 2);
v_val_1463_ = lean_ctor_get(v_stx_1459_, 2);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_stx_1459_, 4);
v_leading_1464_ = lean_ctor_get(v_info_1461_, 0);
lean_inc_ref(v_leading_1464_);
v_pos_1465_ = lean_ctor_get(v_info_1461_, 1);
lean_inc(v_pos_1465_);
v_trailing_1466_ = lean_ctor_get(v_info_1461_, 2);
lean_inc_ref(v_trailing_1466_);
lean_dec_ref_known(v_info_1461_, 4);
v_rawComps_1467_ = l_Lean_Syntax_splitNameLit(v_rawVal_1462_);
v___x_1468_ = l_List_isEmpty___redArg(v_rawComps_1467_);
if (v___x_1468_ == 0)
{
lean_object* v_val_1469_; lean_object* v_nameComps_1470_; lean_object* v___y_1472_; 
v_val_1469_ = l_Lean_Name_eraseMacroScopes(v_val_1463_);
lean_dec(v_val_1463_);
v_nameComps_1470_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1469_, v_nFields_x3f_1460_);
if (lean_obj_tag(v_nFields_x3f_1460_) == 1)
{
lean_object* v_val_1486_; lean_object* v_str_1487_; lean_object* v_startPos_1488_; lean_object* v_stopPos_1489_; lean_object* v___x_1490_; lean_object* v_nPrefix_1491_; lean_object* v___y_1493_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_prefixSz_1499_; lean_object* v___x_1500_; lean_object* v_prefixSz_1501_; lean_object* v___y_1503_; uint8_t v___x_1508_; 
v_val_1486_ = lean_ctor_get(v_nFields_x3f_1460_, 0);
v_str_1487_ = lean_ctor_get(v_rawVal_1462_, 0);
v_startPos_1488_ = lean_ctor_get(v_rawVal_1462_, 1);
v_stopPos_1489_ = lean_ctor_get(v_rawVal_1462_, 2);
v___x_1490_ = l_List_lengthTR___redArg(v_rawComps_1467_);
v_nPrefix_1491_ = lean_nat_sub(v___x_1490_, v_val_1486_);
lean_dec(v___x_1490_);
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1491_);
lean_inc(v_rawComps_1467_);
v___x_1498_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1467_, v_rawComps_1467_, v_nPrefix_1491_, v___x_1497_);
v_prefixSz_1499_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1496_, v___x_1498_);
lean_dec(v___x_1498_);
v___x_1500_ = lean_unsigned_to_nat(1u);
v_prefixSz_1501_ = lean_nat_sub(v_prefixSz_1499_, v___x_1500_);
lean_dec(v_prefixSz_1499_);
v___x_1508_ = lean_nat_dec_le(v_prefixSz_1501_, v___x_1496_);
if (v___x_1508_ == 0)
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_le(v_stopPos_1489_, v_startPos_1488_);
if (v___x_1509_ == 0)
{
lean_inc(v_startPos_1488_);
v___y_1503_ = v_startPos_1488_;
goto v___jp_1502_;
}
else
{
lean_inc(v_stopPos_1489_);
v___y_1503_ = v_stopPos_1489_;
goto v___jp_1502_;
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_prefixSz_1501_);
v___x_1510_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1493_ = v___x_1510_;
goto v___jp_1492_;
}
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = l_List_drop___redArg(v_nPrefix_1491_, v_rawComps_1467_);
lean_dec(v_rawComps_1467_);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___y_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___y_1472_ = v___x_1495_;
goto v___jp_1471_;
}
v___jp_1502_:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_nat_add(v_startPos_1488_, v_prefixSz_1501_);
lean_dec(v_prefixSz_1501_);
v___x_1505_ = lean_nat_dec_le(v_stopPos_1489_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_inc_ref(v_str_1487_);
v___x_1506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1506_, 0, v_str_1487_);
lean_ctor_set(v___x_1506_, 1, v___y_1503_);
lean_ctor_set(v___x_1506_, 2, v___x_1504_);
v___y_1493_ = v___x_1506_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1507_; 
lean_dec(v___x_1504_);
lean_inc(v_stopPos_1489_);
lean_inc_ref(v_str_1487_);
v___x_1507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1507_, 0, v_str_1487_);
lean_ctor_set(v___x_1507_, 1, v___y_1503_);
lean_ctor_set(v___x_1507_, 2, v_stopPos_1489_);
v___y_1493_ = v___x_1507_;
goto v___jp_1492_;
}
}
}
else
{
v___y_1472_ = v_rawComps_1467_;
goto v___jp_1471_;
}
v___jp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = l_List_lengthTR___redArg(v_nameComps_1470_);
v___x_1474_ = l_List_lengthTR___redArg(v___y_1472_);
v___x_1475_ = lean_nat_dec_eq(v___x_1473_, v___x_1474_);
lean_dec(v___x_1474_);
lean_dec(v___x_1473_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec(v___y_1472_);
lean_dec(v_nameComps_1470_);
lean_dec_ref(v_trailing_1466_);
lean_dec(v_pos_1465_);
lean_dec_ref(v_leading_1464_);
lean_dec_ref(v_rawVal_1462_);
v___x_1476_ = lean_box(0);
return v___x_1476_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_comps_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v_seps_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc(v___y_1472_);
v___x_1477_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1470_, v___y_1472_);
v___x_1478_ = lean_box(0);
v_comps_1479_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1462_, v_pos_1465_, v_trailing_1466_, v_leading_1464_, v___x_1477_, v___x_1478_);
v___x_1480_ = lean_array_mk(v___y_1472_);
v___x_1481_ = lean_array_pop(v___x_1480_);
v___x_1482_ = lean_array_to_list(v___x_1481_);
v_seps_1483_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1462_, v_pos_1465_, v___x_1482_, v___x_1478_);
lean_dec(v_pos_1465_);
lean_dec_ref(v_rawVal_1462_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_comps_1479_);
lean_ctor_set(v___x_1484_, 1, v_seps_1483_);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_rawComps_1467_);
lean_dec_ref(v_trailing_1466_);
lean_dec(v_pos_1465_);
lean_dec_ref(v_leading_1464_);
lean_dec(v_val_1463_);
lean_dec_ref(v_rawVal_1462_);
v___x_1511_ = lean_box(0);
return v___x_1511_;
}
}
else
{
lean_object* v___x_1512_; 
lean_dec_ref_known(v_stx_1459_, 4);
lean_dec(v_info_1461_);
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_stx_1459_);
v___x_1513_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__4, &l_Lean_Syntax_identComponents_x3f___closed__4_once, _init_l_Lean_Syntax_identComponents_x3f___closed__4);
v___x_1514_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1515_, lean_object* v_nFields_x3f_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Syntax_identComponents_x3f(v_stx_1515_, v_nFields_x3f_1516_);
lean_dec(v_nFields_x3f_1516_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1518_, lean_object* v_nFields_x3f_1519_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1519_) == 1)
{
lean_object* v_val_1520_; lean_object* v_nameComps_1521_; lean_object* v___x_1522_; lean_object* v_nPrefix_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_namePrefix_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_val_1520_ = lean_ctor_get(v_nFields_x3f_1519_, 0);
v_nameComps_1521_ = l_Lean_Name_components(v_n_1518_);
v___x_1522_ = l_List_lengthTR___redArg(v_nameComps_1521_);
v_nPrefix_1523_ = lean_nat_sub(v___x_1522_, v_val_1520_);
lean_dec(v___x_1522_);
v___x_1524_ = lean_box(0);
v___x_1525_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1523_);
lean_inc(v_nameComps_1521_);
v___x_1526_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1521_, v_nameComps_1521_, v_nPrefix_1523_, v___x_1525_);
v_namePrefix_1527_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1524_, v___x_1526_);
v___x_1528_ = l_List_drop___redArg(v_nPrefix_1523_, v_nameComps_1521_);
lean_dec(v_nameComps_1521_);
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_namePrefix_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Name_components(v_n_1518_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1531_, lean_object* v_nFields_x3f_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1531_, v_nFields_x3f_1532_);
lean_dec(v_nFields_x3f_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_panic_fn_borrowed(v___x_1535_, v_msg_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
if (lean_obj_tag(v_a_1538_) == 0)
{
lean_object* v___x_1540_; 
lean_dec(v_info_1537_);
v___x_1540_ = l_List_reverse___redArg(v_a_1539_);
return v___x_1540_;
}
else
{
lean_object* v_head_1541_; lean_object* v_tail_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1557_; 
v_head_1541_ = lean_ctor_get(v_a_1538_, 0);
v_tail_1542_ = lean_ctor_get(v_a_1538_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1557_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_tail_1542_);
lean_inc(v_head_1541_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1557_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1546_ = 1;
lean_inc(v_head_1541_);
v___x_1547_ = l_Lean_Name_toString(v_head_1541_, v___x_1546_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_string_utf8_byte_size(v___x_1547_);
v___x_1550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1548_);
lean_ctor_set(v___x_1550_, 2, v___x_1549_);
v___x_1551_ = lean_box(0);
lean_inc(v_info_1537_);
v___x_1552_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1552_, 0, v_info_1537_);
lean_ctor_set(v___x_1552_, 1, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v_head_1541_);
lean_ctor_set(v___x_1552_, 3, v___x_1551_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_a_1539_);
lean_ctor_set(v___x_1544_, 0, v___x_1552_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_a_1539_);
v___x_1554_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
v_a_1538_ = v_tail_1542_;
v_a_1539_ = v___x_1554_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1560_ = lean_unsigned_to_nat(9u);
v___x_1561_ = lean_unsigned_to_nat(393u);
v___x_1562_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1563_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1564_ = l_mkPanicMessageWithDecl(v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_, v___x_1559_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1565_, lean_object* v_nFields_x3f_1566_){
_start:
{
if (lean_obj_tag(v_stx_1565_) == 3)
{
lean_object* v_info_1567_; lean_object* v_rawVal_1568_; lean_object* v_val_1569_; lean_object* v_val_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v_info_1567_ = lean_ctor_get(v_stx_1565_, 0);
lean_inc(v_info_1567_);
v_rawVal_1568_ = lean_ctor_get(v_stx_1565_, 1);
v_val_1569_ = lean_ctor_get(v_stx_1565_, 2);
v_val_1570_ = l_Lean_Name_eraseMacroScopes(v_val_1569_);
v___x_1571_ = l_Lean_Name_getNumParts(v_val_1570_);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_dec_le(v___x_1571_, v___x_1572_);
lean_dec(v___x_1571_);
if (v___x_1573_ == 0)
{
if (lean_obj_tag(v_info_1567_) == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Syntax_identComponents_x3f(v_stx_1565_, v_nFields_x3f_1566_);
if (lean_obj_tag(v___x_1574_) == 1)
{
lean_object* v_val_1575_; lean_object* v_fst_1576_; 
lean_dec_ref_known(v_info_1567_, 4);
lean_dec(v_val_1570_);
v_val_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v_fst_1576_ = lean_ctor_get(v_val_1575_, 0);
lean_inc(v_fst_1576_);
lean_dec(v_val_1575_);
return v_fst_1576_;
}
else
{
lean_object* v_nameComps_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v___x_1574_);
v_nameComps_1577_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1570_, v_nFields_x3f_1566_);
v___x_1578_ = lean_box(0);
v___x_1579_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1567_, v_nameComps_1577_, v___x_1578_);
return v___x_1579_;
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec_ref_known(v_stx_1565_, 4);
v___x_1580_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1570_, v_nFields_x3f_1566_);
v___x_1581_ = lean_box(0);
v___x_1582_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1567_, v___x_1580_, v___x_1581_);
return v___x_1582_;
}
}
else
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1591_; 
lean_inc_ref(v_rawVal_1568_);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_stx_1565_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1592_ = lean_ctor_get(v_stx_1565_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_stx_1565_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_stx_1565_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_stx_1565_, 0);
lean_dec(v_unused_1595_);
v___x_1584_ = v_stx_1565_;
v_isShared_1585_ = v_isSharedCheck_1591_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_stx_1565_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1591_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 3, v___x_1586_);
lean_ctor_set(v___x_1584_, 2, v_val_1570_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_info_1567_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_rawVal_1568_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_val_1570_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1586_);
return v___x_1589_;
}
}
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_stx_1565_);
v___x_1596_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1597_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1596_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1598_, lean_object* v_nFields_x3f_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Syntax_identComponents(v_stx_1598_, v_nFields_x3f_1599_);
lean_dec(v_nFields_x3f_1599_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1601_, uint8_t v_firstChoiceOnly_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1603_, 0, v_stx_1601_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1, v_firstChoiceOnly_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1604_, lean_object* v_firstChoiceOnly_1605_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1606_; lean_object* v_res_1607_; 
v_firstChoiceOnly_boxed_1606_ = lean_unbox(v_firstChoiceOnly_1605_);
v_res_1607_ = l_Lean_Syntax_topDown(v_stx_1604_, v_firstChoiceOnly_boxed_1606_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1608_, lean_object* v_____r_1609_, lean_object* v_b_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_b_1610_);
v___x_1612_ = lean_apply_2(v_toPure_1608_, lean_box(0), v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1613_, lean_object* v_toPure_1614_, lean_object* v_____s_1615_){
_start:
{
lean_object* v_fst_1616_; 
v_fst_1616_ = lean_ctor_get(v_____s_1615_, 0);
if (lean_obj_tag(v_fst_1616_) == 0)
{
lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_toPure_1614_);
v_snd_1617_ = lean_ctor_get(v_____s_1615_, 1);
lean_inc(v_snd_1617_);
lean_dec_ref(v_____s_1615_);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_apply_2(v___f_1613_, v___x_1618_, v_snd_1617_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
lean_inc_ref(v_fst_1616_);
lean_dec_ref(v_____s_1615_);
lean_dec(v___f_1613_);
v_val_1620_ = lean_ctor_get(v_fst_1616_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v_fst_1616_, 1);
v___x_1621_ = lean_apply_2(v_toPure_1614_, lean_box(0), v_val_1620_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1622_, lean_object* v_toPure_1623_, lean_object* v___x_1624_, lean_object* v_____do__lift_1625_){
_start:
{
if (lean_obj_tag(v_____do__lift_1625_) == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_____do__lift_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_snd_1622_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = lean_apply_2(v_toPure_1623_, lean_box(0), v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_snd_1622_);
v_a_1630_ = lean_ctor_get(v_____do__lift_1625_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_____do__lift_1625_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1632_ = v_____do__lift_1625_;
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v_____do__lift_1625_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1624_);
lean_ctor_set(v___x_1634_, 1, v_a_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_apply_2(v_toPure_1623_, lean_box(0), v___x_1636_);
return v___x_1637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1640_, lean_object* v___x_1641_, lean_object* v_inst_1642_, lean_object* v_f_1643_, lean_object* v_firstChoiceOnly_1644_, lean_object* v_toBind_1645_, lean_object* v_a_1646_, lean_object* v_x_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1649_; lean_object* v_res_1650_; 
v_firstChoiceOnly_boxed_1649_ = lean_unbox(v_firstChoiceOnly_1644_);
v_res_1650_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1640_, v___x_1641_, v_inst_1642_, v_f_1643_, v_firstChoiceOnly_boxed_1649_, v_toBind_1645_, v_a_1646_, v_x_1647_, v___y_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1654_, lean_object* v_stx_1655_, lean_object* v_inst_1656_, lean_object* v_f_1657_, uint8_t v_firstChoiceOnly_1658_, lean_object* v_toBind_1659_, lean_object* v___f_1660_, lean_object* v___x_1661_, lean_object* v___f_1662_, lean_object* v_____do__lift_1663_){
_start:
{
if (lean_obj_tag(v_____do__lift_1663_) == 0)
{
lean_object* v___x_1664_; 
lean_dec(v___f_1662_);
lean_dec(v___f_1660_);
lean_dec(v_toBind_1659_);
lean_dec(v_f_1657_);
lean_dec_ref(v_inst_1656_);
lean_dec(v_stx_1655_);
v___x_1664_ = lean_apply_2(v_toPure_1654_, lean_box(0), v_____do__lift_1663_);
return v___x_1664_;
}
else
{
if (lean_obj_tag(v_stx_1655_) == 1)
{
lean_object* v_a_1665_; lean_object* v_kind_1666_; lean_object* v_args_1667_; 
lean_dec(v___f_1662_);
v_a_1665_ = lean_ctor_get(v_____do__lift_1663_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v_____do__lift_1663_, 1);
v_kind_1666_ = lean_ctor_get(v_stx_1655_, 1);
lean_inc(v_kind_1666_);
v_args_1667_ = lean_ctor_get(v_stx_1655_, 2);
lean_inc_ref(v_args_1667_);
lean_dec_ref_known(v_stx_1655_, 3);
if (v_firstChoiceOnly_1658_ == 0)
{
lean_dec(v_kind_1666_);
goto v___jp_1668_;
}
else
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1678_ = lean_name_eq(v_kind_1666_, v___x_1677_);
lean_dec(v_kind_1666_);
if (v___x_1678_ == 0)
{
goto v___jp_1668_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec(v___f_1660_);
lean_dec(v_toBind_1659_);
lean_dec(v_toPure_1654_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_array_get(v___x_1661_, v_args_1667_, v___x_1679_);
lean_dec_ref(v_args_1667_);
v___x_1681_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1656_, v_f_1657_, v_firstChoiceOnly_1658_, v___x_1680_, v_a_1665_);
return v___x_1681_;
}
}
v___jp_1668_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; size_t v_sz_1673_; size_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_box(v_firstChoiceOnly_1658_);
lean_inc(v_toBind_1659_);
lean_inc_ref(v_inst_1656_);
v___f_1671_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1671_, 0, v_toPure_1654_);
lean_closure_set(v___f_1671_, 1, v___x_1669_);
lean_closure_set(v___f_1671_, 2, v_inst_1656_);
lean_closure_set(v___f_1671_, 3, v_f_1657_);
lean_closure_set(v___f_1671_, 4, v___x_1670_);
lean_closure_set(v___f_1671_, 5, v_toBind_1659_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1669_);
lean_ctor_set(v___x_1672_, 1, v_a_1665_);
v_sz_1673_ = lean_array_size(v_args_1667_);
v___x_1674_ = ((size_t)0ULL);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1656_, v_args_1667_, v___f_1671_, v_sz_1673_, v___x_1674_, v___x_1672_);
v___x_1676_ = lean_apply_4(v_toBind_1659_, lean_box(0), lean_box(0), v___x_1675_, v___f_1660_);
return v___x_1676_;
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v___f_1660_);
lean_dec(v_toBind_1659_);
lean_dec(v_f_1657_);
lean_dec_ref(v_inst_1656_);
lean_dec(v_stx_1655_);
lean_dec(v_toPure_1654_);
v_a_1682_ = lean_ctor_get(v_____do__lift_1663_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v_____do__lift_1663_, 1);
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_apply_2(v___f_1662_, v___x_1683_, v_a_1682_);
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1685_, lean_object* v_stx_1686_, lean_object* v_inst_1687_, lean_object* v_f_1688_, lean_object* v_firstChoiceOnly_1689_, lean_object* v_toBind_1690_, lean_object* v___f_1691_, lean_object* v___x_1692_, lean_object* v___f_1693_, lean_object* v_____do__lift_1694_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1695_; lean_object* v_res_1696_; 
v_firstChoiceOnly_boxed_1695_ = lean_unbox(v_firstChoiceOnly_1689_);
v_res_1696_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1685_, v_stx_1686_, v_inst_1687_, v_f_1688_, v_firstChoiceOnly_boxed_1695_, v_toBind_1690_, v___f_1691_, v___x_1692_, v___f_1693_, v_____do__lift_1694_);
lean_dec(v___x_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1697_, lean_object* v_f_1698_, uint8_t v_firstChoiceOnly_1699_, lean_object* v_stx_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v_toApplicative_1702_; lean_object* v_toBind_1703_; lean_object* v_toPure_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; 
v_toApplicative_1702_ = lean_ctor_get(v_inst_1697_, 0);
v_toBind_1703_ = lean_ctor_get(v_inst_1697_, 1);
lean_inc_n(v_toBind_1703_, 2);
v_toPure_1704_ = lean_ctor_get(v_toApplicative_1702_, 1);
lean_inc_n(v_toPure_1704_, 3);
v___x_1705_ = lean_box(0);
lean_inc(v_f_1698_);
lean_inc(v_stx_1700_);
v___x_1706_ = lean_apply_2(v_f_1698_, v_stx_1700_, v_b_1701_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1707_, 0, v_toPure_1704_);
lean_inc_ref(v___f_1707_);
v___f_1708_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1708_, 0, v___f_1707_);
lean_closure_set(v___f_1708_, 1, v_toPure_1704_);
v___x_1709_ = lean_box(v_firstChoiceOnly_1699_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1710_, 0, v_toPure_1704_);
lean_closure_set(v___f_1710_, 1, v_stx_1700_);
lean_closure_set(v___f_1710_, 2, v_inst_1697_);
lean_closure_set(v___f_1710_, 3, v_f_1698_);
lean_closure_set(v___f_1710_, 4, v___x_1709_);
lean_closure_set(v___f_1710_, 5, v_toBind_1703_);
lean_closure_set(v___f_1710_, 6, v___f_1708_);
lean_closure_set(v___f_1710_, 7, v___x_1705_);
lean_closure_set(v___f_1710_, 8, v___f_1707_);
v___x_1711_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1706_, v___f_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1712_, lean_object* v___x_1713_, lean_object* v_inst_1714_, lean_object* v_f_1715_, uint8_t v_firstChoiceOnly_1716_, lean_object* v_toBind_1717_, lean_object* v_a_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_snd_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_snd_1721_ = lean_ctor_get(v___y_1720_, 1);
lean_inc_n(v_snd_1721_, 2);
lean_dec_ref(v___y_1720_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1722_, 0, v_snd_1721_);
lean_closure_set(v___f_1722_, 1, v_toPure_1712_);
lean_closure_set(v___f_1722_, 2, v___x_1713_);
v___x_1723_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1714_, v_f_1715_, v_firstChoiceOnly_1716_, v_a_1718_, v_snd_1721_);
v___x_1724_ = lean_apply_4(v_toBind_1717_, lean_box(0), lean_box(0), v___x_1723_, v___f_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1725_, lean_object* v_f_1726_, lean_object* v_firstChoiceOnly_1727_, lean_object* v_stx_1728_, lean_object* v_b_1729_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1730_; lean_object* v_res_1731_; 
v_firstChoiceOnly_boxed_1730_ = lean_unbox(v_firstChoiceOnly_1727_);
v_res_1731_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1725_, v_f_1726_, v_firstChoiceOnly_boxed_1730_, v_stx_1728_, v_b_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1732_, lean_object* v_inst_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_f_1735_, uint8_t v_firstChoiceOnly_1736_, lean_object* v_stx_1737_, lean_object* v_b_1738_, lean_object* v_inst_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1733_, v_f_1735_, v_firstChoiceOnly_1736_, v_stx_1737_, v_b_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1741_, lean_object* v_inst_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_f_1744_, lean_object* v_firstChoiceOnly_1745_, lean_object* v_stx_1746_, lean_object* v_b_1747_, lean_object* v_inst_1748_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1749_; lean_object* v_res_1750_; 
v_firstChoiceOnly_boxed_1749_ = lean_unbox(v_firstChoiceOnly_1745_);
v_res_1750_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1741_, v_inst_1742_, v_00_u03b2_1743_, v_f_1744_, v_firstChoiceOnly_boxed_1749_, v_stx_1746_, v_b_1747_, v_inst_1748_);
lean_dec(v_inst_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1751_, lean_object* v_____do__lift_1752_){
_start:
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v_____do__lift_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v_____do__lift_1752_);
v___x_1754_ = lean_apply_2(v_toPure_1751_, lean_box(0), v_a_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1755_, lean_object* v_toBind_1756_, lean_object* v___f_1757_, lean_object* v_00_u03b2_1758_, lean_object* v_x_1759_, lean_object* v_init_1760_, lean_object* v_f_1761_){
_start:
{
uint8_t v_firstChoiceOnly_1762_; lean_object* v_stx_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_firstChoiceOnly_1762_ = lean_ctor_get_uint8(v_x_1759_, sizeof(void*)*1);
v_stx_1763_ = lean_ctor_get(v_x_1759_, 0);
lean_inc(v_stx_1763_);
lean_dec_ref(v_x_1759_);
v___x_1764_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1755_, v_f_1761_, v_firstChoiceOnly_1762_, v_stx_1763_, v_init_1760_);
v___x_1765_ = lean_apply_4(v_toBind_1756_, lean_box(0), lean_box(0), v___x_1764_, v___f_1757_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1766_){
_start:
{
lean_object* v_toApplicative_1767_; lean_object* v_toBind_1768_; lean_object* v_toPure_1769_; lean_object* v___f_1770_; lean_object* v___f_1771_; 
v_toApplicative_1767_ = lean_ctor_get(v_inst_1766_, 0);
v_toBind_1768_ = lean_ctor_get(v_inst_1766_, 1);
lean_inc(v_toBind_1768_);
v_toPure_1769_ = lean_ctor_get(v_toApplicative_1767_, 1);
lean_inc(v_toPure_1769_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1770_, 0, v_toPure_1769_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1771_, 0, v_inst_1766_);
lean_closure_set(v___f_1771_, 1, v_toBind_1768_);
lean_closure_set(v___f_1771_, 2, v___f_1770_);
return v___f_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1772_, lean_object* v_inst_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1776_, lean_object* v_val_1777_){
_start:
{
if (lean_obj_tag(v_info_1776_) == 0)
{
lean_object* v_leading_1778_; lean_object* v_trailing_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_leading_1778_ = lean_ctor_get(v_info_1776_, 0);
lean_inc_ref(v_leading_1778_);
v_trailing_1779_ = lean_ctor_get(v_info_1776_, 2);
lean_inc_ref(v_trailing_1779_);
lean_dec_ref_known(v_info_1776_, 4);
v___x_1780_ = lean_substring_tostring(v_leading_1778_);
v___x_1781_ = lean_string_append(v___x_1780_, v_val_1777_);
v___x_1782_ = lean_substring_tostring(v_trailing_1779_);
v___x_1783_ = lean_string_append(v___x_1781_, v___x_1782_);
lean_dec_ref(v___x_1782_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec(v_info_1776_);
v___x_1784_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1785_ = lean_string_append(v___x_1784_, v_val_1777_);
v___x_1786_ = lean_string_append(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1787_, lean_object* v_val_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1787_, v_val_1788_);
lean_dec_ref(v_val_1788_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1790_, lean_object* v_as_1791_, size_t v_sz_1792_, size_t v_i_1793_, lean_object* v_b_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_usize_dec_lt(v_i_1793_, v_sz_1792_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_b_1794_);
return v___x_1796_;
}
else
{
lean_object* v_snd_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1824_; 
v_snd_1797_ = lean_ctor_get(v_b_1794_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_b_1794_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v_b_1794_, 0);
lean_dec(v_unused_1825_);
v___x_1799_ = v_b_1794_;
v_isShared_1800_ = v_isSharedCheck_1824_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snd_1797_);
lean_dec(v_b_1794_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1824_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_a_1801_; lean_object* v___x_1802_; 
v_a_1801_ = lean_array_uget_borrowed(v_as_1791_, v_i_1793_);
lean_inc(v_snd_1797_);
lean_inc(v_a_1801_);
v___x_1802_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1790_, v_a_1801_, v_snd_1797_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1803_; 
lean_del_object(v___x_1799_);
lean_dec(v_snd_1797_);
v___x_1803_ = lean_box(0);
return v___x_1803_;
}
else
{
lean_object* v_val_1804_; 
v_val_1804_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_val_1804_);
if (lean_obj_tag(v_val_1804_) == 0)
{
lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1814_; 
v_isSharedCheck_1814_ = !lean_is_exclusive(v_val_1804_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_val_1804_, 0);
lean_dec(v_unused_1815_);
v___x_1806_ = v_val_1804_;
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
else
{
lean_dec(v_val_1804_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1809_ = v___x_1799_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_snd_1797_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set_tag(v___x_1806_, 1);
lean_ctor_set(v___x_1806_, 0, v___x_1809_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_dec_ref_known(v___x_1802_, 1);
lean_dec(v_snd_1797_);
v_a_1816_ = lean_ctor_get(v_val_1804_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v_val_1804_, 1);
v___x_1817_ = lean_box(0);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v_a_1816_);
lean_ctor_set(v___x_1799_, 0, v___x_1817_);
v___x_1819_ = v___x_1799_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_a_1816_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
size_t v___x_1820_; size_t v___x_1821_; 
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1793_, v___x_1820_);
v_i_1793_ = v___x_1821_;
v_b_1794_ = v___x_1819_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_){
_start:
{
lean_object* v_array_1829_; lean_object* v_start_1830_; lean_object* v_stop_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1850_; 
v_array_1829_ = lean_ctor_get(v_a_1827_, 0);
v_start_1830_ = lean_ctor_get(v_a_1827_, 1);
v_stop_1831_ = lean_ctor_get(v_a_1827_, 2);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1833_ = v_a_1827_;
v_isShared_1834_ = v_isSharedCheck_1850_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_stop_1831_);
lean_inc(v_start_1830_);
lean_inc(v_array_1829_);
lean_dec(v_a_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1850_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_nat_dec_lt(v_start_1830_, v_stop_1831_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_del_object(v___x_1833_);
lean_dec(v_stop_1831_);
lean_dec(v_start_1830_);
lean_dec_ref(v_array_1829_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_b_1828_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_array_fget_borrowed(v_array_1829_, v_start_1830_);
lean_inc(v___x_1837_);
v___x_1838_ = l_Lean_Syntax_reprint(v___x_1837_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; 
lean_del_object(v___x_1833_);
lean_dec(v_stop_1831_);
lean_dec(v_start_1830_);
lean_dec_ref(v_array_1829_);
v___x_1839_ = lean_box(0);
return v___x_1839_;
}
else
{
lean_object* v_val_1840_; uint8_t v___x_1841_; 
v_val_1840_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1841_ = lean_string_dec_eq(v_val_1826_, v_val_1840_);
lean_dec(v_val_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_del_object(v___x_1833_);
lean_dec(v_stop_1831_);
lean_dec(v_start_1830_);
lean_dec_ref(v_array_1829_);
v___x_1842_ = lean_box(0);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_unsigned_to_nat(1u);
v___x_1845_ = lean_nat_add(v_start_1830_, v___x_1844_);
lean_dec(v_start_1830_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1845_);
v___x_1847_ = v___x_1833_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_array_1829_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_stop_1831_);
v___x_1847_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v_a_1827_ = v___x_1847_;
v_b_1828_ = v___x_1843_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1851_, lean_object* v_stx_1852_, lean_object* v_b_1853_){
_start:
{
lean_object* v_b_1855_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___x_1869_; lean_object* v_a_1871_; 
v___x_1869_ = lean_box(0);
switch(lean_obj_tag(v_stx_1852_))
{
case 2:
{
lean_object* v_info_1880_; lean_object* v_val_1881_; lean_object* v___x_1882_; lean_object* v_s_1883_; 
v_info_1880_ = lean_ctor_get(v_stx_1852_, 0);
v_val_1881_ = lean_ctor_get(v_stx_1852_, 1);
lean_inc(v_info_1880_);
v___x_1882_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1880_, v_val_1881_);
v_s_1883_ = lean_string_append(v_b_1853_, v___x_1882_);
lean_dec_ref(v___x_1882_);
v_a_1871_ = v_s_1883_;
goto v___jp_1870_;
}
case 3:
{
lean_object* v_rawVal_1884_; lean_object* v_info_1885_; lean_object* v_str_1886_; lean_object* v_startPos_1887_; lean_object* v_stopPos_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_s_1891_; 
v_rawVal_1884_ = lean_ctor_get(v_stx_1852_, 1);
v_info_1885_ = lean_ctor_get(v_stx_1852_, 0);
v_str_1886_ = lean_ctor_get(v_rawVal_1884_, 0);
v_startPos_1887_ = lean_ctor_get(v_rawVal_1884_, 1);
v_stopPos_1888_ = lean_ctor_get(v_rawVal_1884_, 2);
v___x_1889_ = lean_string_utf8_extract(v_str_1886_, v_startPos_1887_, v_stopPos_1888_);
lean_inc(v_info_1885_);
v___x_1890_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1885_, v___x_1889_);
lean_dec_ref(v___x_1889_);
v_s_1891_ = lean_string_append(v_b_1853_, v___x_1890_);
lean_dec_ref(v___x_1890_);
v_a_1871_ = v_s_1891_;
goto v___jp_1870_;
}
case 1:
{
lean_object* v_kind_1892_; lean_object* v_args_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_kind_1892_ = lean_ctor_get(v_stx_1852_, 1);
v_args_1893_ = lean_ctor_get(v_stx_1852_, 2);
v___x_1894_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1895_ = lean_name_eq(v_kind_1892_, v___x_1894_);
if (v___x_1895_ == 0)
{
v_a_1871_ = v_b_1853_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_unsigned_to_nat(0u);
v___x_1897_ = lean_array_get_borrowed(v___x_1869_, v_args_1893_, v___x_1896_);
lean_inc(v___x_1897_);
v___x_1898_ = l_Lean_Syntax_reprint(v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref_known(v_stx_1852_, 3);
lean_dec_ref(v_b_1853_);
v___x_1899_ = lean_box(0);
return v___x_1899_;
}
else
{
lean_object* v_val_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_val_1900_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_array_get_size(v_args_1893_);
lean_inc_ref(v_args_1893_);
v___x_1903_ = l_Array_toSubarray___redArg(v_args_1893_, v___x_1901_, v___x_1902_);
v___x_1904_ = lean_box(0);
v___x_1905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1900_, v___x_1903_, v___x_1904_);
lean_dec(v_val_1900_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1906_; 
lean_dec_ref_known(v_stx_1852_, 3);
lean_dec_ref(v_b_1853_);
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
else
{
lean_dec_ref_known(v___x_1905_, 1);
v_a_1871_ = v_b_1853_;
goto v___jp_1870_;
}
}
}
}
default: 
{
v_a_1871_ = v_b_1853_;
goto v___jp_1870_;
}
}
v___jp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_b_1855_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
v___jp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___y_1859_);
v_sz_1863_ = lean_array_size(v___y_1860_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1851_, v___y_1860_, v_sz_1863_, v___x_1864_, v___x_1862_);
lean_dec_ref(v___y_1860_);
if (lean_obj_tag(v___x_1865_) == 0)
{
return v___x_1861_;
}
else
{
lean_object* v_val_1866_; lean_object* v_fst_1867_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v_fst_1867_ = lean_ctor_get(v_val_1866_, 0);
if (lean_obj_tag(v_fst_1867_) == 0)
{
lean_object* v_snd_1868_; 
v_snd_1868_ = lean_ctor_get(v_val_1866_, 1);
lean_inc(v_snd_1868_);
lean_dec(v_val_1866_);
v_b_1855_ = v_snd_1868_;
goto v___jp_1854_;
}
else
{
lean_inc_ref(v_fst_1867_);
lean_dec(v_val_1866_);
return v_fst_1867_;
}
}
}
v___jp_1870_:
{
if (lean_obj_tag(v_stx_1852_) == 1)
{
if (v_firstChoiceOnly_1851_ == 0)
{
lean_object* v_args_1872_; 
v_args_1872_ = lean_ctor_get(v_stx_1852_, 2);
lean_inc_ref(v_args_1872_);
lean_dec_ref_known(v_stx_1852_, 3);
v___y_1859_ = v_a_1871_;
v___y_1860_ = v_args_1872_;
goto v___jp_1858_;
}
else
{
lean_object* v_kind_1873_; lean_object* v_args_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v_kind_1873_ = lean_ctor_get(v_stx_1852_, 1);
lean_inc(v_kind_1873_);
v_args_1874_ = lean_ctor_get(v_stx_1852_, 2);
lean_inc_ref(v_args_1874_);
lean_dec_ref_known(v_stx_1852_, 3);
v___x_1875_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1876_ = lean_name_eq(v_kind_1873_, v___x_1875_);
lean_dec(v_kind_1873_);
if (v___x_1876_ == 0)
{
v___y_1859_ = v_a_1871_;
v___y_1860_ = v_args_1874_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get(v___x_1869_, v_args_1874_, v___x_1877_);
lean_dec_ref(v_args_1874_);
v_stx_1852_ = v___x_1878_;
v_b_1853_ = v_a_1871_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1852_);
v_b_1855_ = v_a_1871_;
goto v___jp_1854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1907_){
_start:
{
lean_object* v_s_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v_s_1908_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1909_ = 1;
v___x_1910_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1909_, v_stx_1907_, v_s_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_box(0);
return v___x_1911_;
}
else
{
lean_object* v_val_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
v_val_1912_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1914_ = v___x_1910_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_val_1912_);
lean_dec(v___x_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_a_1916_; lean_object* v___x_1918_; 
v_a_1916_ = lean_ctor_get(v_val_1912_, 0);
lean_inc(v_a_1916_);
lean_dec(v_val_1912_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v_a_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1921_, lean_object* v_a_1922_, lean_object* v_b_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1921_, v_a_1922_, v_b_1923_);
lean_dec_ref(v_val_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1925_, lean_object* v_as_1926_, lean_object* v_sz_1927_, lean_object* v_i_1928_, lean_object* v_b_1929_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1930_; size_t v_sz_boxed_1931_; size_t v_i_boxed_1932_; lean_object* v_res_1933_; 
v_firstChoiceOnly_boxed_1930_ = lean_unbox(v_firstChoiceOnly_1925_);
v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1927_);
lean_dec(v_sz_1927_);
v_i_boxed_1932_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1930_, v_as_1926_, v_sz_boxed_1931_, v_i_boxed_1932_, v_b_1929_);
lean_dec_ref(v_as_1926_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1934_, lean_object* v_stx_1935_, lean_object* v_b_1936_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1937_; lean_object* v_res_1938_; 
v_firstChoiceOnly_boxed_1937_ = lean_unbox(v_firstChoiceOnly_1934_);
v_res_1938_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1937_, v_stx_1935_, v_b_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1939_, lean_object* v_inst_1940_, lean_object* v_R_1941_, lean_object* v_a_1942_, lean_object* v_b_1943_, lean_object* v_c_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1939_, v_a_1942_, v_b_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1946_, lean_object* v_inst_1947_, lean_object* v_R_1948_, lean_object* v_a_1949_, lean_object* v_b_1950_, lean_object* v_c_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1946_, v_inst_1947_, v_R_1948_, v_a_1949_, v_b_1950_, v_c_1951_);
lean_dec_ref(v_val_1946_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1961_, lean_object* v_stx_1962_){
_start:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Lean_Syntax_isMissing(v_stx_1962_);
if (v___x_1964_ == 0)
{
if (lean_obj_tag(v_stx_1962_) == 1)
{
lean_object* v_kind_1965_; lean_object* v_args_1966_; 
v_kind_1965_ = lean_ctor_get(v_stx_1962_, 1);
v_args_1966_ = lean_ctor_get(v_stx_1962_, 2);
if (v_firstChoiceOnly_1961_ == 0)
{
goto v___jp_1967_;
}
else
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1977_ = lean_name_eq(v_kind_1965_, v___x_1976_);
if (v___x_1977_ == 0)
{
goto v___jp_1967_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_array_get_borrowed(v___x_1978_, v_args_1966_, v___x_1979_);
v_stx_1962_ = v___x_1980_;
goto _start;
}
}
v___jp_1967_:
{
lean_object* v___x_1968_; size_t v_sz_1969_; size_t v___x_1970_; lean_object* v___x_1971_; lean_object* v_fst_1972_; 
v___x_1968_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1969_ = lean_array_size(v_args_1966_);
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1961_, v_args_1966_, v_sz_1969_, v___x_1970_, v___x_1968_);
v_fst_1972_ = lean_ctor_get(v___x_1971_, 0);
if (lean_obj_tag(v_fst_1972_) == 0)
{
lean_object* v_snd_1973_; lean_object* v___x_1974_; 
v_snd_1973_ = lean_ctor_get(v___x_1971_, 1);
lean_inc(v_snd_1973_);
lean_dec_ref(v___x_1971_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_snd_1973_);
return v___x_1974_;
}
else
{
lean_object* v_val_1975_; 
lean_inc_ref(v_fst_1972_);
lean_dec_ref(v___x_1971_);
v_val_1975_ = lean_ctor_get(v_fst_1972_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_fst_1972_, 1);
return v_val_1975_;
}
}
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1982_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1983_ = lean_box(v___x_1964_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v___x_1963_);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1987_, lean_object* v_as_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_b_1991_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1992_ == 0)
{
return v_b_1991_;
}
else
{
lean_object* v_snd_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2011_; 
v_snd_1993_ = lean_ctor_get(v_b_1991_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_b_1991_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_b_1991_, 0);
lean_dec(v_unused_2012_);
v___x_1995_ = v_b_1991_;
v_isShared_1996_ = v_isSharedCheck_2011_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_snd_1993_);
lean_dec(v_b_1991_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2011_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_array_uget_borrowed(v_as_1988_, v_i_1990_);
v___x_1998_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1987_, v_a_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1999_);
v___x_2001_ = v___x_1995_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_snd_1993_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec(v_snd_1993_);
v_a_2003_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2004_ = lean_box(0);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v_a_2003_);
lean_ctor_set(v___x_1995_, 0, v___x_2004_);
v___x_2006_ = v___x_1995_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_a_2003_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
size_t v___x_2007_; size_t v___x_2008_; 
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_add(v_i_1990_, v___x_2007_);
v_i_1990_ = v___x_2008_;
v_b_1991_ = v___x_2006_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_2013_, lean_object* v_as_2014_, lean_object* v_sz_2015_, lean_object* v_i_2016_, lean_object* v_b_2017_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2018_; size_t v_sz_boxed_2019_; size_t v_i_boxed_2020_; lean_object* v_res_2021_; 
v_firstChoiceOnly_boxed_2018_ = lean_unbox(v_firstChoiceOnly_2013_);
v_sz_boxed_2019_ = lean_unbox_usize(v_sz_2015_);
lean_dec(v_sz_2015_);
v_i_boxed_2020_ = lean_unbox_usize(v_i_2016_);
lean_dec(v_i_2016_);
v_res_2021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_2018_, v_as_2014_, v_sz_boxed_2019_, v_i_boxed_2020_, v_b_2017_);
lean_dec_ref(v_as_2014_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_2022_, lean_object* v_stx_2023_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2024_; lean_object* v_res_2025_; 
v_firstChoiceOnly_boxed_2024_ = lean_unbox(v_firstChoiceOnly_2022_);
v_res_2025_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_2024_, v_stx_2023_);
lean_dec(v_stx_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_2026_){
_start:
{
uint8_t v___x_2027_; lean_object* v___y_2029_; lean_object* v___x_2033_; lean_object* v_a_2034_; 
v___x_2027_ = 0;
v___x_2033_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_2027_, v_stx_2026_);
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___y_2029_ = v_a_2034_;
goto v___jp_2028_;
v___jp_2028_:
{
lean_object* v_fst_2030_; 
v_fst_2030_ = lean_ctor_get(v___y_2029_, 0);
lean_inc(v_fst_2030_);
lean_dec_ref(v___y_2029_);
if (lean_obj_tag(v_fst_2030_) == 0)
{
return v___x_2027_;
}
else
{
lean_object* v_val_2031_; uint8_t v___x_2032_; 
v_val_2031_ = lean_ctor_get(v_fst_2030_, 0);
lean_inc(v_val_2031_);
lean_dec_ref_known(v_fst_2030_, 1);
v___x_2032_ = lean_unbox(v_val_2031_);
lean_dec(v_val_2031_);
return v___x_2032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_2035_){
_start:
{
uint8_t v_res_2036_; lean_object* v_r_2037_; 
v_res_2036_ = l_Lean_Syntax_hasMissing(v_stx_2035_);
lean_dec(v_stx_2035_);
v_r_2037_ = lean_box(v_res_2036_);
return v_r_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_2038_, lean_object* v_stx_2039_, lean_object* v_b_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_2038_, v_stx_2039_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_2042_, lean_object* v_stx_2043_, lean_object* v_b_2044_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2045_; lean_object* v_res_2046_; 
v_firstChoiceOnly_boxed_2045_ = lean_unbox(v_firstChoiceOnly_2042_);
v_res_2046_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_2045_, v_stx_2043_, v_b_2044_);
lean_dec_ref(v_b_2044_);
lean_dec(v_stx_2043_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_2047_, uint8_t v_canonicalOnly_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Syntax_getPos_x3f(v_stx_2047_, v_canonicalOnly_2048_);
if (lean_obj_tag(v___x_2049_) == 1)
{
lean_object* v_val_2050_; lean_object* v___x_2051_; 
v_val_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_val_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2047_, v_canonicalOnly_2048_);
if (lean_obj_tag(v___x_2051_) == 1)
{
lean_object* v_val_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2060_; 
v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_val_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_val_2050_);
lean_ctor_set(v___x_2056_, 1, v_val_2052_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2056_);
v___x_2058_ = v___x_2054_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v___x_2051_);
lean_dec(v_val_2050_);
v___x_2061_ = lean_box(0);
return v___x_2061_;
}
}
else
{
lean_object* v___x_2062_; 
lean_dec(v___x_2049_);
v___x_2062_ = lean_box(0);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_2063_, lean_object* v_canonicalOnly_2064_){
_start:
{
uint8_t v_canonicalOnly_boxed_2065_; lean_object* v_res_2066_; 
v_canonicalOnly_boxed_2065_ = lean_unbox(v_canonicalOnly_2064_);
v_res_2066_ = l_Lean_Syntax_getRange_x3f(v_stx_2063_, v_canonicalOnly_boxed_2065_);
lean_dec(v_stx_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_2067_, uint8_t v_canonicalOnly_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Syntax_getPos_x3f(v_stx_2067_, v_canonicalOnly_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_box(0);
return v___x_2070_;
}
else
{
lean_object* v_val_2071_; lean_object* v___x_2072_; 
v_val_2071_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2072_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_2067_, v_canonicalOnly_2068_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; 
lean_dec(v_val_2071_);
v___x_2073_ = lean_box(0);
return v___x_2073_;
}
else
{
lean_object* v_val_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_val_2074_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v___x_2072_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_val_2074_);
lean_dec(v___x_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_val_2071_);
lean_ctor_set(v___x_2078_, 1, v_val_2074_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_2083_, lean_object* v_canonicalOnly_2084_){
_start:
{
uint8_t v_canonicalOnly_boxed_2085_; lean_object* v_res_2086_; 
v_canonicalOnly_boxed_2085_ = lean_unbox(v_canonicalOnly_2084_);
v_res_2086_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_2083_, v_canonicalOnly_boxed_2085_);
lean_dec(v_stx_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_2087_, uint8_t v_canonical_2088_){
_start:
{
lean_object* v_start_2089_; lean_object* v_stop_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2099_; 
v_start_2089_ = lean_ctor_get(v_range_2087_, 0);
v_stop_2090_ = lean_ctor_get(v_range_2087_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_range_2087_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2092_ = v_range_2087_;
v_isShared_2093_ = v_isSharedCheck_2099_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_stop_2090_);
lean_inc(v_start_2089_);
lean_dec(v_range_2087_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2099_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2094_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2094_, 0, v_start_2089_);
lean_ctor_set(v___x_2094_, 1, v_stop_2090_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*2, v_canonical_2088_);
v___x_2095_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 2);
lean_ctor_set(v___x_2092_, 1, v___x_2095_);
lean_ctor_set(v___x_2092_, 0, v___x_2094_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2100_, lean_object* v_canonical_2101_){
_start:
{
uint8_t v_canonical_boxed_2102_; lean_object* v_res_2103_; 
v_canonical_boxed_2102_ = lean_unbox(v_canonical_2101_);
v_res_2103_ = l_Lean_Syntax_ofRange(v_range_2100_, v_canonical_boxed_2102_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2108_, 0, v_stx_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
lean_ctor_set(v___x_2108_, 2, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2109_, lean_object* v_stx_2110_){
_start:
{
lean_object* v_parents_2111_; lean_object* v_idxs_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_parents_2111_ = lean_ctor_get(v_t_2109_, 1);
v_idxs_2112_ = lean_ctor_get(v_t_2109_, 2);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_t_2109_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_t_2109_, 0);
lean_dec(v_unused_2120_);
v___x_2114_ = v_t_2109_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_idxs_2112_);
lean_inc(v_parents_2111_);
lean_dec(v_t_2109_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_stx_2110_);
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_stx_2110_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_parents_2111_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_idxs_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2121_, lean_object* v_idx_2122_){
_start:
{
lean_object* v_cur_2123_; lean_object* v_parents_2124_; lean_object* v_idxs_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2145_; 
v_cur_2123_ = lean_ctor_get(v_t_2121_, 0);
v_parents_2124_ = lean_ctor_get(v_t_2121_, 1);
v_idxs_2125_ = lean_ctor_get(v_t_2121_, 2);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_t_2121_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2127_ = v_t_2121_;
v_isShared_2128_ = v_isSharedCheck_2145_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_idxs_2125_);
lean_inc(v_parents_2124_);
lean_inc(v_cur_2123_);
lean_dec(v_t_2121_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2145_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = l_Lean_Syntax_getNumArgs(v_cur_2123_);
v___x_2130_ = lean_nat_dec_lt(v_idx_2122_, v___x_2129_);
lean_dec(v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_array_push(v_parents_2124_, v_cur_2123_);
v___x_2133_ = lean_array_push(v_idxs_2125_, v_idx_2122_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 2, v___x_2133_);
lean_ctor_set(v___x_2127_, 1, v___x_2132_);
lean_ctor_set(v___x_2127_, 0, v___x_2131_);
v___x_2135_ = v___x_2127_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2137_ = l_Lean_Syntax_getArg(v_cur_2123_, v_idx_2122_);
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_Syntax_setArg(v_cur_2123_, v_idx_2122_, v___x_2138_);
v___x_2140_ = lean_array_push(v_parents_2124_, v___x_2139_);
v___x_2141_ = lean_array_push(v_idxs_2125_, v_idx_2122_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 2, v___x_2141_);
lean_ctor_set(v___x_2127_, 1, v___x_2140_);
lean_ctor_set(v___x_2127_, 0, v___x_2137_);
v___x_2143_ = v___x_2127_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2146_){
_start:
{
lean_object* v_cur_2147_; lean_object* v_parents_2148_; lean_object* v_idxs_2149_; lean_object* v___y_2151_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_cur_2147_ = lean_ctor_get(v_t_2146_, 0);
v_parents_2148_ = lean_ctor_get(v_t_2146_, 1);
v_idxs_2149_ = lean_ctor_get(v_t_2146_, 2);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_array_get_size(v_parents_2148_);
v___x_2157_ = lean_nat_dec_lt(v___x_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
return v_t_2146_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
lean_inc_ref(v_idxs_2149_);
lean_inc_ref(v_parents_2148_);
lean_inc(v_cur_2147_);
lean_dec_ref(v_t_2146_);
v___x_2158_ = lean_box(0);
v___x_2159_ = lean_array_get_size(v_idxs_2149_);
v___x_2160_ = lean_unsigned_to_nat(1u);
v___x_2161_ = lean_nat_sub(v___x_2159_, v___x_2160_);
v___x_2162_ = lean_array_get_borrowed(v___x_2155_, v_idxs_2149_, v___x_2161_);
lean_dec(v___x_2161_);
v___x_2163_ = lean_nat_sub(v___x_2156_, v___x_2160_);
v___x_2164_ = lean_array_get_borrowed(v___x_2158_, v_parents_2148_, v___x_2163_);
lean_dec(v___x_2163_);
v___x_2165_ = l_Lean_Syntax_getNumArgs(v___x_2164_);
v___x_2166_ = lean_nat_dec_lt(v___x_2162_, v___x_2165_);
lean_dec(v___x_2165_);
if (v___x_2166_ == 0)
{
lean_dec(v_cur_2147_);
lean_inc(v___x_2164_);
v___y_2151_ = v___x_2164_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2167_; 
lean_inc(v___x_2164_);
v___x_2167_ = l_Lean_Syntax_setArg(v___x_2164_, v___x_2162_, v_cur_2147_);
v___y_2151_ = v___x_2167_;
goto v___jp_2150_;
}
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_array_pop(v_parents_2148_);
v___x_2153_ = lean_array_pop(v_idxs_2149_);
v___x_2154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2154_, 0, v___y_2151_);
lean_ctor_set(v___x_2154_, 1, v___x_2152_);
lean_ctor_set(v___x_2154_, 2, v___x_2153_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2168_){
_start:
{
lean_object* v_parents_2169_; lean_object* v_idxs_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_parents_2169_ = lean_ctor_get(v_t_2168_, 1);
v_idxs_2170_ = lean_ctor_get(v_t_2168_, 2);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_array_get_size(v_parents_2169_);
v___x_2173_ = lean_nat_dec_lt(v___x_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
return v_t_2168_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_inc_ref(v_idxs_2170_);
v___x_2174_ = l_Lean_Syntax_Traverser_up(v_t_2168_);
v___x_2175_ = lean_array_get_size(v_idxs_2170_);
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_sub(v___x_2175_, v___x_2176_);
v___x_2178_ = lean_array_get(v___x_2171_, v_idxs_2170_, v___x_2177_);
lean_dec(v___x_2177_);
lean_dec_ref(v_idxs_2170_);
v___x_2179_ = lean_nat_sub(v___x_2178_, v___x_2176_);
lean_dec(v___x_2178_);
v___x_2180_ = l_Lean_Syntax_Traverser_down(v___x_2174_, v___x_2179_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2181_){
_start:
{
lean_object* v_parents_2182_; lean_object* v_idxs_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_parents_2182_ = lean_ctor_get(v_t_2181_, 1);
v_idxs_2183_ = lean_ctor_get(v_t_2181_, 2);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_array_get_size(v_parents_2182_);
v___x_2186_ = lean_nat_dec_lt(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
return v_t_2181_;
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_inc_ref(v_idxs_2183_);
v___x_2187_ = l_Lean_Syntax_Traverser_up(v_t_2181_);
v___x_2188_ = lean_array_get_size(v_idxs_2183_);
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = lean_nat_sub(v___x_2188_, v___x_2189_);
v___x_2191_ = lean_array_get(v___x_2184_, v_idxs_2183_, v___x_2190_);
lean_dec(v___x_2190_);
lean_dec_ref(v_idxs_2183_);
v___x_2192_ = lean_nat_add(v___x_2191_, v___x_2189_);
lean_dec(v___x_2191_);
v___x_2193_ = l_Lean_Syntax_Traverser_down(v___x_2187_, v___x_2192_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2194_){
_start:
{
lean_object* v_cur_2195_; 
v_cur_2195_ = lean_ctor_get(v_self_2194_, 0);
lean_inc(v_cur_2195_);
return v_cur_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2196_);
lean_dec_ref(v_self_2196_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2199_, lean_object* v_t_2200_){
_start:
{
lean_object* v_toApplicative_2201_; lean_object* v_toFunctor_2202_; lean_object* v_map_2203_; lean_object* v_get_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; 
v_toApplicative_2201_ = lean_ctor_get(v_inst_2199_, 0);
lean_inc_ref(v_toApplicative_2201_);
lean_dec_ref(v_inst_2199_);
v_toFunctor_2202_ = lean_ctor_get(v_toApplicative_2201_, 0);
lean_inc_ref(v_toFunctor_2202_);
lean_dec_ref(v_toApplicative_2201_);
v_map_2203_ = lean_ctor_get(v_toFunctor_2202_, 0);
lean_inc(v_map_2203_);
lean_dec_ref(v_toFunctor_2202_);
v_get_2204_ = lean_ctor_get(v_t_2200_, 0);
lean_inc(v_get_2204_);
lean_dec_ref(v_t_2200_);
v___f_2205_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2206_ = lean_apply_4(v_map_2203_, lean_box(0), lean_box(0), v___f_2205_, v_get_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2207_, lean_object* v_inst_2208_, lean_object* v_t_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2208_, v_t_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2211_, lean_object* v_s_2212_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = l_Lean_Syntax_Traverser_setCur(v_s_2212_, v_stx_2211_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2216_, lean_object* v_stx_2217_){
_start:
{
lean_object* v_modifyGet_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; 
v_modifyGet_2218_ = lean_ctor_get(v_t_2216_, 2);
lean_inc(v_modifyGet_2218_);
lean_dec_ref(v_t_2216_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2219_, 0, v_stx_2217_);
v___x_2220_ = lean_apply_2(v_modifyGet_2218_, lean_box(0), v___f_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2221_, lean_object* v_t_2222_, lean_object* v_stx_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2222_, v_stx_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2225_, lean_object* v_s_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = l_Lean_Syntax_Traverser_down(v_s_2226_, v_idx_2225_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2230_, lean_object* v_idx_2231_){
_start:
{
lean_object* v_modifyGet_2232_; lean_object* v___f_2233_; lean_object* v___x_2234_; 
v_modifyGet_2232_ = lean_ctor_get(v_t_2230_, 2);
lean_inc(v_modifyGet_2232_);
lean_dec_ref(v_t_2230_);
v___f_2233_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2233_, 0, v_idx_2231_);
v___x_2234_ = lean_apply_2(v_modifyGet_2232_, lean_box(0), v___f_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2235_, lean_object* v_t_2236_, lean_object* v_idx_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2236_, v_idx_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2239_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_box(0);
v___x_2241_ = l_Lean_Syntax_Traverser_up(v_s_2239_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2244_){
_start:
{
lean_object* v_modifyGet_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; 
v_modifyGet_2245_ = lean_ctor_get(v_t_2244_, 2);
lean_inc(v_modifyGet_2245_);
lean_dec_ref(v_t_2244_);
v___f_2246_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2247_ = lean_apply_2(v_modifyGet_2245_, lean_box(0), v___f_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2248_, lean_object* v_t_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_box(0);
v___x_2253_ = l_Lean_Syntax_Traverser_left(v_s_2251_);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2256_){
_start:
{
lean_object* v_modifyGet_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; 
v_modifyGet_2257_ = lean_ctor_get(v_t_2256_, 2);
lean_inc(v_modifyGet_2257_);
lean_dec_ref(v_t_2256_);
v___f_2258_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2259_ = lean_apply_2(v_modifyGet_2257_, lean_box(0), v___f_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2260_, lean_object* v_t_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_box(0);
v___x_2265_ = l_Lean_Syntax_Traverser_right(v_s_2263_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2268_){
_start:
{
lean_object* v_modifyGet_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; 
v_modifyGet_2269_ = lean_ctor_get(v_t_2268_, 2);
lean_inc(v_modifyGet_2269_);
lean_dec_ref(v_t_2268_);
v___f_2270_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2271_ = lean_apply_2(v_modifyGet_2269_, lean_box(0), v___f_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2272_, lean_object* v_t_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2275_, lean_object* v_st_2276_){
_start:
{
lean_object* v_idxs_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_idxs_2277_ = lean_ctor_get(v_st_2276_, 2);
v___x_2278_ = lean_array_get_size(v_idxs_2277_);
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = lean_nat_sub(v___x_2278_, v___x_2279_);
v___x_2281_ = lean_nat_dec_lt(v___x_2280_, v___x_2278_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec(v___x_2280_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_apply_2(v_toPure_2275_, lean_box(0), v___x_2282_);
return v___x_2283_;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_array_fget_borrowed(v_idxs_2277_, v___x_2280_);
lean_dec(v___x_2280_);
lean_inc(v___x_2284_);
v___x_2285_ = lean_apply_2(v_toPure_2275_, lean_box(0), v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2286_, lean_object* v_st_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2286_, v_st_2287_);
lean_dec_ref(v_st_2287_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2289_, lean_object* v_t_2290_){
_start:
{
lean_object* v_toApplicative_2291_; lean_object* v_toBind_2292_; lean_object* v_get_2293_; lean_object* v_toPure_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; 
v_toApplicative_2291_ = lean_ctor_get(v_inst_2289_, 0);
lean_inc_ref(v_toApplicative_2291_);
v_toBind_2292_ = lean_ctor_get(v_inst_2289_, 1);
lean_inc(v_toBind_2292_);
lean_dec_ref(v_inst_2289_);
v_get_2293_ = lean_ctor_get(v_t_2290_, 0);
lean_inc(v_get_2293_);
lean_dec_ref(v_t_2290_);
v_toPure_2294_ = lean_ctor_get(v_toApplicative_2291_, 1);
lean_inc(v_toPure_2294_);
lean_dec_ref(v_toApplicative_2291_);
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2295_, 0, v_toPure_2294_);
v___x_2296_ = lean_apply_4(v_toBind_2292_, lean_box(0), lean_box(0), v_get_2293_, v___f_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2297_, lean_object* v_inst_2298_, lean_object* v_t_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2298_, v_t_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2301_, lean_object* v_i_2302_){
_start:
{
lean_object* v_args_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_args_2303_ = lean_ctor_get(v_n_2301_, 2);
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_array_get_borrowed(v___x_2304_, v_args_2303_, v_i_2302_);
v___x_2306_ = l_Lean_Syntax_getId(v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2307_, lean_object* v_i_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_SyntaxNode_getIdAt(v_n_2307_, v_i_2308_);
lean_dec(v_i_2308_);
lean_dec(v_n_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2312_ = lean_box(2);
v___x_2313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v___x_2311_);
lean_ctor_set(v___x_2313_, 2, v_args_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2319_){
_start:
{
if (lean_obj_tag(v_x_2319_) == 1)
{
lean_object* v_kind_2320_; 
v_kind_2320_ = lean_ctor_get(v_x_2319_, 1);
if (lean_obj_tag(v_kind_2320_) == 1)
{
lean_object* v_pre_2321_; lean_object* v_str_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_pre_2321_ = lean_ctor_get(v_kind_2320_, 0);
v_str_2322_ = lean_ctor_get(v_kind_2320_, 1);
v___x_2323_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2324_ = lean_string_dec_eq(v_str_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2326_ = lean_string_dec_eq(v_str_2322_, v___x_2325_);
if (v___x_2326_ == 0)
{
return v___x_2326_;
}
else
{
if (lean_obj_tag(v_pre_2321_) == 1)
{
lean_object* v_pre_2327_; 
v_pre_2327_ = lean_ctor_get(v_pre_2321_, 0);
if (lean_obj_tag(v_pre_2327_) == 1)
{
lean_object* v_pre_2328_; 
v_pre_2328_ = lean_ctor_get(v_pre_2327_, 0);
if (lean_obj_tag(v_pre_2328_) == 1)
{
lean_object* v_pre_2329_; 
v_pre_2329_ = lean_ctor_get(v_pre_2328_, 0);
if (lean_obj_tag(v_pre_2329_) == 0)
{
lean_object* v_str_2330_; lean_object* v_str_2331_; lean_object* v_str_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_str_2330_ = lean_ctor_get(v_pre_2321_, 1);
v_str_2331_ = lean_ctor_get(v_pre_2327_, 1);
v_str_2332_ = lean_ctor_get(v_pre_2328_, 1);
v___x_2333_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2334_ = lean_string_dec_eq(v_str_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
return v___x_2324_;
}
else
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2336_ = lean_string_dec_eq(v_str_2331_, v___x_2335_);
if (v___x_2336_ == 0)
{
return v___x_2336_;
}
else
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2338_ = lean_string_dec_eq(v_str_2330_, v___x_2337_);
return v___x_2338_;
}
}
}
else
{
return v___x_2324_;
}
}
else
{
return v___x_2324_;
}
}
else
{
return v___x_2324_;
}
}
else
{
return v___x_2324_;
}
}
}
else
{
return v___x_2324_;
}
}
else
{
uint8_t v___x_2339_; 
v___x_2339_ = 0;
return v___x_2339_;
}
}
else
{
uint8_t v___x_2340_; 
v___x_2340_ = 0;
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2341_){
_start:
{
uint8_t v_res_2342_; lean_object* v_r_2343_; 
v_res_2342_ = l_Lean_Syntax_isQuot(v_x_2341_);
lean_dec(v_x_2341_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2349_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___y_2353_; uint8_t v___x_2359_; 
v___x_2350_ = l_Lean_Syntax_getNumArgs(v_stx_2349_);
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2359_ = lean_nat_dec_eq(v___x_2350_, v___x_2351_);
lean_dec(v___x_2350_);
if (v___x_2359_ == 0)
{
v___y_2353_ = v_stx_2349_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = l_Lean_Syntax_getArg(v_stx_2349_, v___x_2360_);
lean_dec(v_stx_2349_);
v___y_2353_ = v___x_2361_;
goto v___jp_2352_;
}
v___jp_2352_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2353_);
v___x_2355_ = l_Lean_Syntax_isOfKind(v___y_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Syntax_getArg(v___y_2353_, v___x_2351_);
lean_dec(v___y_2353_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_unsigned_to_nat(3u);
v___x_2358_ = l_Lean_Syntax_getArg(v___y_2353_, v___x_2357_);
lean_dec(v___y_2353_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2363_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 1)
{
lean_object* v_kind_2364_; 
v_kind_2364_ = lean_ctor_get(v_x_2363_, 1);
if (lean_obj_tag(v_kind_2364_) == 1)
{
lean_object* v_str_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_str_2365_ = lean_ctor_get(v_kind_2364_, 1);
v___x_2366_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2367_ = lean_string_dec_eq(v_str_2365_, v___x_2366_);
return v___x_2367_;
}
else
{
uint8_t v___x_2368_; 
v___x_2368_ = 0;
return v___x_2368_;
}
}
else
{
uint8_t v___x_2369_; 
v___x_2369_ = 0;
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2370_){
_start:
{
uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_res_2371_ = l_Lean_Syntax_isAntiquot(v_x_2370_);
lean_dec(v_x_2370_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object* v___x_2373_, uint8_t v___x_2374_, lean_object* v_as_2375_, size_t v_i_2376_, size_t v_stop_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = lean_usize_dec_eq(v_i_2376_, v_stop_2377_);
if (v___x_2378_ == 0)
{
uint8_t v___x_2379_; uint8_t v___y_2381_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2379_ = 1;
v___x_2385_ = lean_array_uget_borrowed(v_as_2375_, v_i_2376_);
v___x_2386_ = l_Lean_Syntax_isAntiquot(v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_nat_dec_lt(v___x_2387_, v___x_2373_);
v___y_2381_ = v___x_2388_;
goto v___jp_2380_;
}
else
{
v___y_2381_ = v___x_2374_;
goto v___jp_2380_;
}
v___jp_2380_:
{
if (v___y_2381_ == 0)
{
size_t v___x_2382_; size_t v___x_2383_; 
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2376_, v___x_2382_);
v_i_2376_ = v___x_2383_;
goto _start;
}
else
{
return v___x_2379_;
}
}
}
else
{
uint8_t v___x_2389_; 
v___x_2389_ = 0;
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___x_2390_, lean_object* v___x_2391_, lean_object* v_as_2392_, lean_object* v_i_2393_, lean_object* v_stop_2394_){
_start:
{
uint8_t v___x_341__boxed_2395_; size_t v_i_boxed_2396_; size_t v_stop_boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v___x_341__boxed_2395_ = lean_unbox(v___x_2391_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2393_);
lean_dec(v_i_2393_);
v_stop_boxed_2397_ = lean_unbox_usize(v_stop_2394_);
lean_dec(v_stop_2394_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2390_, v___x_341__boxed_2395_, v_as_2392_, v_i_boxed_2396_, v_stop_boxed_2397_);
lean_dec_ref(v_as_2392_);
lean_dec(v___x_2390_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2400_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = l_Lean_Syntax_isAntiquot(v_stx_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2400_);
v___x_2403_ = l_Lean_Syntax_isOfKind(v_stx_2400_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_dec(v_stx_2400_);
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = l_Lean_Syntax_getNumArgs(v_stx_2400_);
v___x_2406_ = lean_nat_dec_lt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec(v___x_2405_);
lean_dec(v_stx_2400_);
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2407_ = l_Lean_Syntax_getArgs(v_stx_2400_);
lean_dec(v_stx_2400_);
v___x_2408_ = lean_array_get_size(v___x_2407_);
v___x_2409_ = lean_nat_dec_lt(v___x_2404_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_dec_ref(v___x_2407_);
lean_dec(v___x_2405_);
return v___x_2406_;
}
else
{
if (v___x_2409_ == 0)
{
lean_dec_ref(v___x_2407_);
lean_dec(v___x_2405_);
return v___x_2406_;
}
else
{
size_t v___x_2410_; size_t v___x_2411_; uint8_t v___x_2412_; 
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = lean_usize_of_nat(v___x_2408_);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2405_, v___x_2401_, v___x_2407_, v___x_2410_, v___x_2411_);
lean_dec_ref(v___x_2407_);
lean_dec(v___x_2405_);
if (v___x_2412_ == 0)
{
return v___x_2409_;
}
else
{
return v___x_2401_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_2400_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Lean_Syntax_isAntiquots(v_stx_2413_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2416_){
_start:
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2416_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v_stx_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
return v_stx_2416_;
}
else
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2419_);
lean_dec(v_stx_2416_);
return v___x_2420_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2423_ = l_Lean_mkAtom(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2427_ = lean_unsigned_to_nat(4u);
v___x_2428_ = lean_mk_empty_array_with_capacity(v___x_2427_);
v___x_2429_ = lean_array_push(v___x_2428_, v___x_2426_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2438_ = l_Lean_mkAtom(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2439_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2440_ = lean_unsigned_to_nat(2u);
v___x_2441_ = lean_mk_empty_array_with_capacity(v___x_2440_);
v___x_2442_ = lean_array_push(v___x_2441_, v___x_2439_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2454_ = l_Lean_mkAtom(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2457_ = l_Lean_mkAtom(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2458_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2459_ = lean_unsigned_to_nat(3u);
v___x_2460_ = lean_mk_empty_array_with_capacity(v___x_2459_);
v___x_2461_ = lean_array_push(v___x_2460_, v___x_2458_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2462_, lean_object* v_term_2463_, lean_object* v_nesting_2464_, lean_object* v_name_2465_, uint8_t v_isPseudoKind_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_nesting_2471_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2490_; uint8_t v___x_2498_; 
v___x_2467_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2468_ = lean_mk_array(v_nesting_2464_, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2470_ = lean_box(2);
v_nesting_2471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2471_, 0, v___x_2470_);
lean_ctor_set(v_nesting_2471_, 1, v___x_2469_);
lean_ctor_set(v_nesting_2471_, 2, v___x_2468_);
v___x_2498_ = l_Lean_Syntax_isIdent(v_term_2463_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2463_);
v___x_2500_ = l_Lean_Syntax_isOfKind(v_term_2463_, v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2501_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2502_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2503_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2504_ = lean_array_push(v___x_2503_, v_term_2463_);
v___x_2505_ = lean_array_push(v___x_2504_, v___x_2502_);
v___x_2506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2470_);
lean_ctor_set(v___x_2506_, 1, v___x_2501_);
lean_ctor_set(v___x_2506_, 2, v___x_2505_);
v___y_2490_ = v___x_2506_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_unsigned_to_nat(0u);
v___x_2508_ = l_Lean_Syntax_getArg(v_term_2463_, v___x_2507_);
lean_dec(v_term_2463_);
v___y_2490_ = v___x_2508_;
goto v___jp_2489_;
}
}
else
{
v___y_2490_ = v_term_2463_;
goto v___jp_2489_;
}
v___jp_2472_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_inc(v___y_2475_);
v___x_2476_ = l_Lean_Name_append(v_kind_2462_, v___y_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2478_ = l_Lean_Name_append(v___x_2476_, v___x_2477_);
v___x_2479_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2480_ = lean_array_push(v___x_2479_, v_nesting_2471_);
v___x_2481_ = lean_array_push(v___x_2480_, v___y_2473_);
v___x_2482_ = lean_array_push(v___x_2481_, v___y_2474_);
v___x_2483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2470_);
lean_ctor_set(v___x_2483_, 1, v___x_2478_);
lean_ctor_set(v___x_2483_, 2, v___x_2482_);
return v___x_2483_;
}
v___jp_2484_:
{
if (v_isPseudoKind_2466_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_box(0);
v___y_2473_ = v___y_2485_;
v___y_2474_ = v___y_2486_;
v___y_2475_ = v___x_2487_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2473_ = v___y_2485_;
v___y_2474_ = v___y_2486_;
v___y_2475_ = v___x_2488_;
goto v___jp_2472_;
}
}
v___jp_2489_:
{
if (lean_obj_tag(v_name_2465_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2485_ = v___y_2490_;
v___y_2486_ = v___x_2491_;
goto v___jp_2484_;
}
else
{
lean_object* v_val_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_val_2492_ = lean_ctor_get(v_name_2465_, 0);
lean_inc(v_val_2492_);
lean_dec_ref_known(v_name_2465_, 1);
v___x_2493_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2494_ = l_Lean_mkAtom(v_val_2492_);
v___x_2495_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2496_ = lean_array_push(v___x_2495_, v___x_2494_);
v___x_2497_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2470_);
lean_ctor_set(v___x_2497_, 1, v___x_2493_);
lean_ctor_set(v___x_2497_, 2, v___x_2496_);
v___y_2485_ = v___y_2490_;
v___y_2486_ = v___x_2497_;
goto v___jp_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2509_, lean_object* v_term_2510_, lean_object* v_nesting_2511_, lean_object* v_name_2512_, lean_object* v_isPseudoKind_2513_){
_start:
{
uint8_t v_isPseudoKind_boxed_2514_; lean_object* v_res_2515_; 
v_isPseudoKind_boxed_2514_ = lean_unbox(v_isPseudoKind_2513_);
v_res_2515_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2509_, v_term_2510_, v_nesting_2511_, v_name_2512_, v_isPseudoKind_boxed_2514_);
return v_res_2515_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2517_ = lean_unsigned_to_nat(1u);
v___x_2518_ = l_Lean_Syntax_getArg(v_stx_2516_, v___x_2517_);
v___x_2519_ = l_Lean_Syntax_getArgs(v___x_2518_);
lean_dec(v___x_2518_);
v___x_2520_ = lean_array_get_size(v___x_2519_);
lean_dec_ref(v___x_2519_);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_nat_dec_eq(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
uint8_t v___x_2523_; 
v___x_2523_ = 1;
return v___x_2523_;
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = 0;
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2525_);
lean_dec(v_stx_2525_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2528_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = l_Lean_Syntax_isAntiquot(v_stx_2528_);
if (v___x_2529_ == 0)
{
return v_stx_2528_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = l_Lean_Syntax_getArg(v_stx_2528_, v___x_2530_);
v___x_2532_ = l_Lean_Syntax_getArgs(v___x_2531_);
lean_dec(v___x_2531_);
v___x_2533_ = lean_array_pop(v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2535_ = lean_box(2);
v___x_2536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2534_);
lean_ctor_set(v___x_2536_, 2, v___x_2533_);
v___x_2537_ = l_Lean_Syntax_setArg(v_stx_2528_, v___x_2530_, v___x_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2538_){
_start:
{
lean_object* v___y_2540_; uint8_t v___x_2551_; 
v___x_2551_ = l_Lean_Syntax_isAntiquot(v_stx_2538_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_unsigned_to_nat(3u);
v___x_2553_ = l_Lean_Syntax_getArg(v_stx_2538_, v___x_2552_);
v___y_2540_ = v___x_2553_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_unsigned_to_nat(2u);
v___x_2555_ = l_Lean_Syntax_getArg(v_stx_2538_, v___x_2554_);
v___y_2540_ = v___x_2555_;
goto v___jp_2539_;
}
v___jp_2539_:
{
uint8_t v___x_2541_; 
v___x_2541_ = l_Lean_Syntax_isIdent(v___y_2540_);
if (v___x_2541_ == 0)
{
uint8_t v___x_2542_; 
v___x_2542_ = l_Lean_Syntax_isAtom(v___y_2540_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = l_Lean_Syntax_getArg(v___y_2540_, v___x_2543_);
lean_dec(v___y_2540_);
return v___x_2544_;
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2545_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_mk_empty_array_with_capacity(v___x_2546_);
v___x_2548_ = lean_array_push(v___x_2547_, v___y_2540_);
v___x_2549_ = lean_box(2);
v___x_2550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2545_);
lean_ctor_set(v___x_2550_, 2, v___x_2548_);
return v___x_2550_;
}
}
else
{
return v___y_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2556_);
lean_dec(v_stx_2556_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 1)
{
lean_object* v_kind_2559_; 
v_kind_2559_ = lean_ctor_get(v_x_2558_, 1);
if (lean_obj_tag(v_kind_2559_) == 1)
{
lean_object* v_pre_2560_; lean_object* v_str_2561_; 
v_pre_2560_ = lean_ctor_get(v_kind_2559_, 0);
v_str_2561_ = lean_ctor_get(v_kind_2559_, 1);
if (lean_obj_tag(v_pre_2560_) == 1)
{
lean_object* v_pre_2567_; lean_object* v_str_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_pre_2567_ = lean_ctor_get(v_pre_2560_, 0);
v_str_2568_ = lean_ctor_get(v_pre_2560_, 1);
v___x_2569_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2570_ = lean_string_dec_eq(v_str_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2572_ = lean_string_dec_eq(v_str_2561_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_box(0);
return v___x_2573_;
}
else
{
goto v___jp_2562_;
}
}
else
{
lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2574_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2575_ = lean_string_dec_eq(v_str_2561_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_box(0);
return v___x_2576_;
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_box(v___x_2575_);
lean_inc(v_pre_2567_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_pre_2567_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
}
else
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2581_ = lean_string_dec_eq(v_str_2561_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_box(0);
return v___x_2582_;
}
else
{
goto v___jp_2562_;
}
}
v___jp_2562_:
{
uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2563_ = 0;
v___x_2564_ = lean_box(v___x_2563_);
lean_inc(v_pre_2560_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_pre_2560_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
else
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_box(0);
return v___x_2583_;
}
}
else
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_box(0);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2585_);
lean_dec(v_x_2585_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2587_, size_t v_i_2588_, size_t v_stop_2589_, lean_object* v_b_2590_){
_start:
{
lean_object* v___y_2592_; uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_eq(v_i_2588_, v_stop_2589_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_array_uget_borrowed(v_as_2587_, v_i_2588_);
v___x_2598_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2597_);
if (lean_obj_tag(v___x_2598_) == 0)
{
v___y_2592_ = v_b_2590_;
goto v___jp_2591_;
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2600_; 
v_val_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = lean_array_push(v_b_2590_, v_val_2599_);
v___y_2592_ = v___x_2600_;
goto v___jp_2591_;
}
}
else
{
return v_b_2590_;
}
v___jp_2591_:
{
size_t v___x_2593_; size_t v___x_2594_; 
v___x_2593_ = ((size_t)1ULL);
v___x_2594_ = lean_usize_add(v_i_2588_, v___x_2593_);
v_i_2588_ = v___x_2594_;
v_b_2590_ = v___y_2592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2601_, lean_object* v_i_2602_, lean_object* v_stop_2603_, lean_object* v_b_2604_){
_start:
{
size_t v_i_boxed_2605_; size_t v_stop_boxed_2606_; lean_object* v_res_2607_; 
v_i_boxed_2605_ = lean_unbox_usize(v_i_2602_);
lean_dec(v_i_2602_);
v_stop_boxed_2606_ = lean_unbox_usize(v_stop_2603_);
lean_dec(v_stop_2603_);
v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2601_, v_i_boxed_2605_, v_stop_boxed_2606_, v_b_2604_);
lean_dec_ref(v_as_2601_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2610_, lean_object* v_start_2611_, lean_object* v_stop_2612_){
_start:
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2614_ = lean_nat_dec_lt(v_start_2611_, v_stop_2612_);
if (v___x_2614_ == 0)
{
return v___x_2613_;
}
else
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = lean_array_get_size(v_as_2610_);
v___x_2616_ = lean_nat_dec_le(v_stop_2612_, v___x_2615_);
if (v___x_2616_ == 0)
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_nat_dec_lt(v_start_2611_, v___x_2615_);
if (v___x_2617_ == 0)
{
return v___x_2613_;
}
else
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_usize_of_nat(v_start_2611_);
v___x_2619_ = lean_usize_of_nat(v___x_2615_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2610_, v___x_2618_, v___x_2619_, v___x_2613_);
return v___x_2620_;
}
}
else
{
size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_usize_of_nat(v_start_2611_);
v___x_2622_ = lean_usize_of_nat(v_stop_2612_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2610_, v___x_2621_, v___x_2622_, v___x_2613_);
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2624_, lean_object* v_start_2625_, lean_object* v_stop_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2624_, v_start_2625_, v_stop_2626_);
lean_dec(v_stop_2626_);
lean_dec(v_start_2625_);
lean_dec_ref(v_as_2624_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2628_){
_start:
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2628_);
v___x_2630_ = l_Lean_Syntax_isOfKind(v_stx_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2628_);
lean_dec(v_stx_2628_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_box(0);
return v___x_2632_;
}
else
{
lean_object* v_val_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_val_2633_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_val_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
return v___x_2635_;
}
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2636_ = l_Lean_Syntax_getArgs(v_stx_2628_);
lean_dec(v_stx_2628_);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_array_get_size(v___x_2636_);
v___x_2639_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2636_, v___x_2637_, v___x_2638_);
lean_dec_ref(v___x_2636_);
v___x_2640_ = lean_array_to_list(v___x_2639_);
return v___x_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2642_){
_start:
{
if (lean_obj_tag(v_x_2642_) == 1)
{
lean_object* v_kind_2643_; 
v_kind_2643_ = lean_ctor_get(v_x_2642_, 1);
if (lean_obj_tag(v_kind_2643_) == 1)
{
lean_object* v_pre_2644_; lean_object* v_str_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_pre_2644_ = lean_ctor_get(v_kind_2643_, 0);
v_str_2645_ = lean_ctor_get(v_kind_2643_, 1);
v___x_2646_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2647_ = lean_string_dec_eq(v_str_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_box(0);
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; 
lean_inc(v_pre_2644_);
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_pre_2644_);
return v___x_2649_;
}
}
else
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_box(0);
return v___x_2650_;
}
}
else
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_box(0);
return v___x_2651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2652_);
lean_dec(v_x_2652_);
return v_res_2653_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2654_);
if (lean_obj_tag(v___x_2655_) == 0)
{
uint8_t v___x_2656_; 
v___x_2656_ = 0;
return v___x_2656_;
}
else
{
uint8_t v___x_2657_; 
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = 1;
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2658_);
lean_dec(v_stx_2658_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2661_){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = lean_unsigned_to_nat(3u);
v___x_2663_ = l_Lean_Syntax_getArg(v_stx_2661_, v___x_2662_);
v___x_2664_ = l_Lean_Syntax_getArgs(v___x_2663_);
lean_dec(v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2665_);
lean_dec(v_stx_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2667_){
_start:
{
uint8_t v___x_2668_; 
v___x_2668_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_unsigned_to_nat(1u);
v___x_2670_ = l_Lean_Syntax_getArg(v_stx_2667_, v___x_2669_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_unsigned_to_nat(5u);
v___x_2672_ = l_Lean_Syntax_getArg(v_stx_2667_, v___x_2671_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2673_);
lean_dec(v_stx_2673_);
return v_res_2674_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2680_ = l_Lean_mkAtom(v___x_2679_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2683_ = l_Lean_mkAtom(v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2684_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2685_ = lean_unsigned_to_nat(6u);
v___x_2686_ = lean_mk_empty_array_with_capacity(v___x_2685_);
v___x_2687_ = lean_array_push(v___x_2686_, v___x_2684_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2688_, lean_object* v_contents_2689_, lean_object* v_suffix_2690_, lean_object* v_nesting_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v_nesting_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2692_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2693_ = lean_mk_array(v_nesting_2691_, v___x_2692_);
v___x_2694_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2695_ = lean_box(2);
v_nesting_2696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2696_, 0, v___x_2695_);
lean_ctor_set(v_nesting_2696_, 1, v___x_2694_);
lean_ctor_set(v_nesting_2696_, 2, v___x_2693_);
v___x_2697_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2698_ = l_Lean_Name_append(v_kind_2688_, v___x_2697_);
v___x_2699_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2695_);
lean_ctor_set(v___x_2700_, 1, v___x_2694_);
lean_ctor_set(v___x_2700_, 2, v_contents_2689_);
v___x_2701_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2702_ = l_Lean_mkAtom(v_suffix_2690_);
v___x_2703_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2704_ = lean_array_push(v___x_2703_, v_nesting_2696_);
v___x_2705_ = lean_array_push(v___x_2704_, v___x_2699_);
v___x_2706_ = lean_array_push(v___x_2705_, v___x_2700_);
v___x_2707_ = lean_array_push(v___x_2706_, v___x_2701_);
v___x_2708_ = lean_array_push(v___x_2707_, v___x_2702_);
v___x_2709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2695_);
lean_ctor_set(v___x_2709_, 1, v___x_2698_);
lean_ctor_set(v___x_2709_, 2, v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2711_){
_start:
{
if (lean_obj_tag(v_x_2711_) == 1)
{
lean_object* v_kind_2712_; 
v_kind_2712_ = lean_ctor_get(v_x_2711_, 1);
if (lean_obj_tag(v_kind_2712_) == 1)
{
lean_object* v_pre_2713_; lean_object* v_str_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_pre_2713_ = lean_ctor_get(v_kind_2712_, 0);
v_str_2714_ = lean_ctor_get(v_kind_2712_, 1);
v___x_2715_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2716_ = lean_string_dec_eq(v_str_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_box(0);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; 
lean_inc(v_pre_2713_);
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_pre_2713_);
return v___x_2718_;
}
}
else
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_box(0);
return v___x_2719_;
}
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_box(0);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2721_);
lean_dec(v_x_2721_);
return v_res_2722_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2723_);
if (lean_obj_tag(v___x_2724_) == 0)
{
uint8_t v___x_2725_; 
v___x_2725_ = 0;
return v___x_2725_;
}
else
{
uint8_t v___x_2726_; 
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = 1;
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2727_){
_start:
{
uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_res_2728_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2727_);
lean_dec(v_stx_2727_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_Syntax_getArg(v_stx_2730_, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2733_);
lean_dec(v_stx_2733_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2737_, lean_object* v_inner_2738_, lean_object* v_suffix_2739_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2740_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2741_ = l_Lean_Name_append(v_kind_2737_, v___x_2740_);
v___x_2742_ = l_Lean_mkAtom(v_suffix_2739_);
v___x_2743_ = lean_unsigned_to_nat(2u);
v___x_2744_ = lean_mk_empty_array_with_capacity(v___x_2743_);
v___x_2745_ = lean_array_push(v___x_2744_, v_inner_2738_);
v___x_2746_ = lean_array_push(v___x_2745_, v___x_2742_);
v___x_2747_ = lean_box(2);
v___x_2748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v___x_2741_);
lean_ctor_set(v___x_2748_, 2, v___x_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2752_){
_start:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2754_ = l_Lean_Syntax_isOfKind(v_stx_2752_, v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2755_){
_start:
{
uint8_t v_res_2756_; lean_object* v_r_2757_; 
v_res_2756_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2755_);
v_r_2757_ = lean_box(v_res_2756_);
return v_r_2757_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2758_){
_start:
{
uint8_t v___x_2759_; 
v___x_2759_ = l_Lean_Syntax_isAntiquot(v_stx_2758_);
if (v___x_2759_ == 0)
{
uint8_t v___x_2760_; 
v___x_2760_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2758_);
if (v___x_2760_ == 0)
{
uint8_t v___x_2761_; 
v___x_2761_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2758_);
if (v___x_2761_ == 0)
{
uint8_t v___x_2762_; 
v___x_2762_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2758_);
return v___x_2762_;
}
else
{
lean_dec(v_stx_2758_);
return v___x_2761_;
}
}
else
{
lean_dec(v_stx_2758_);
return v___x_2760_;
}
}
else
{
lean_dec(v_stx_2758_);
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2763_){
_start:
{
uint8_t v_res_2764_; lean_object* v_r_2765_; 
v_res_2764_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2763_);
v_r_2765_ = lean_box(v_res_2764_);
return v_r_2765_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2769_, lean_object* v_stx_2770_, lean_object* v_visit_2771_, lean_object* v_stack_2772_, lean_object* v_accept_2773_, lean_object* v_a_2774_, lean_object* v_b_2775_){
_start:
{
lean_object* v_a_2777_; uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_lt(v_a_2774_, v_upperBound_2769_);
if (v___x_2781_ == 0)
{
lean_dec(v_a_2774_);
lean_dec_ref(v_accept_2773_);
lean_dec(v_stack_2772_);
lean_dec_ref(v_visit_2771_);
lean_dec(v_stx_2770_);
lean_inc_ref(v_b_2775_);
return v_b_2775_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2784_ = l_Lean_Syntax_getArg(v_stx_2770_, v_a_2774_);
lean_inc_ref(v_visit_2771_);
lean_inc(v___x_2784_);
v___x_2785_ = lean_apply_1(v_visit_2771_, v___x_2784_);
v___x_2786_ = lean_unbox(v___x_2785_);
if (v___x_2786_ == 0)
{
lean_dec(v___x_2784_);
v_a_2777_ = v___x_2783_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc(v_a_2774_);
lean_inc(v_stx_2770_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_stx_2770_);
lean_ctor_set(v___x_2787_, 1, v_a_2774_);
lean_inc(v_stack_2772_);
v___x_2788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v_stack_2772_);
lean_inc_ref(v_accept_2773_);
lean_inc_ref(v_visit_2771_);
v___x_2789_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2771_, v_accept_2773_, v___x_2788_, v___x_2784_);
if (lean_obj_tag(v___x_2789_) == 1)
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v_a_2774_);
lean_dec_ref(v_accept_2773_);
lean_dec(v_stack_2772_);
lean_dec_ref(v_visit_2771_);
lean_dec(v_stx_2770_);
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___x_2782_);
return v___x_2791_;
}
else
{
lean_dec(v___x_2789_);
v_a_2777_ = v___x_2783_;
goto v___jp_2776_;
}
}
}
v___jp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_unsigned_to_nat(1u);
v___x_2779_ = lean_nat_add(v_a_2774_, v___x_2778_);
lean_dec(v_a_2774_);
v_a_2774_ = v___x_2779_;
v_b_2775_ = v_a_2777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2792_, lean_object* v_accept_2793_, lean_object* v_stack_2794_, lean_object* v_stx_2795_){
_start:
{
lean_object* v___x_2796_; uint8_t v___x_2797_; 
lean_inc_ref(v_accept_2793_);
lean_inc(v_stx_2795_);
v___x_2796_ = lean_apply_1(v_accept_2793_, v_stx_2795_);
v___x_2797_ = lean_unbox(v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_fst_2803_; 
v___x_2798_ = l_Lean_Syntax_getNumArgs(v_stx_2795_);
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_box(0);
v___x_2801_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2802_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2798_, v_stx_2795_, v_visit_2792_, v_stack_2794_, v_accept_2793_, v___x_2799_, v___x_2801_);
lean_dec(v___x_2798_);
v_fst_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_fst_2803_);
lean_dec_ref(v___x_2802_);
if (lean_obj_tag(v_fst_2803_) == 0)
{
return v___x_2800_;
}
else
{
lean_object* v_val_2804_; 
v_val_2804_ = lean_ctor_get(v_fst_2803_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v_fst_2803_, 1);
return v_val_2804_;
}
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_dec_ref(v_accept_2793_);
lean_dec_ref(v_visit_2792_);
v___x_2805_ = lean_unsigned_to_nat(0u);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_stx_2795_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v_stack_2794_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2809_, lean_object* v_stx_2810_, lean_object* v_visit_2811_, lean_object* v_stack_2812_, lean_object* v_accept_2813_, lean_object* v_a_2814_, lean_object* v_b_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2809_, v_stx_2810_, v_visit_2811_, v_stack_2812_, v_accept_2813_, v_a_2814_, v_b_2815_);
lean_dec_ref(v_b_2815_);
lean_dec(v_upperBound_2809_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2817_, lean_object* v_stx_2818_, lean_object* v_visit_2819_, lean_object* v_stack_2820_, lean_object* v_accept_2821_, lean_object* v_inst_2822_, lean_object* v_R_2823_, lean_object* v_a_2824_, lean_object* v_b_2825_, lean_object* v_c_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2817_, v_stx_2818_, v_visit_2819_, v_stack_2820_, v_accept_2821_, v_a_2824_, v_b_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2828_, lean_object* v_stx_2829_, lean_object* v_visit_2830_, lean_object* v_stack_2831_, lean_object* v_accept_2832_, lean_object* v_inst_2833_, lean_object* v_R_2834_, lean_object* v_a_2835_, lean_object* v_b_2836_, lean_object* v_c_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2828_, v_stx_2829_, v_visit_2830_, v_stack_2831_, v_accept_2832_, v_inst_2833_, v_R_2834_, v_a_2835_, v_b_2836_, v_c_2837_);
lean_dec_ref(v_b_2836_);
lean_dec(v_upperBound_2828_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2839_, lean_object* v_visit_2840_, lean_object* v_accept_2841_){
_start:
{
lean_object* v___x_2842_; uint8_t v___x_2843_; 
lean_inc_ref(v_visit_2840_);
lean_inc(v_root_2839_);
v___x_2842_ = lean_apply_1(v_visit_2840_, v_root_2839_);
v___x_2843_ = lean_unbox(v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; 
lean_dec_ref(v_accept_2841_);
lean_dec_ref(v_visit_2840_);
lean_dec(v_root_2839_);
v___x_2844_ = lean_box(0);
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_box(0);
v___x_2846_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2840_, v_accept_2841_, v___x_2845_, v_root_2839_);
return v___x_2846_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2847_, lean_object* v_x_2848_, lean_object* v_p_2849_){
_start:
{
if (lean_obj_tag(v_p_2849_) == 0)
{
lean_dec_ref(v_x_2848_);
return v___x_2847_;
}
else
{
lean_object* v_fst_2850_; lean_object* v_val_2851_; uint8_t v___x_2852_; 
v_fst_2850_ = lean_ctor_get(v_x_2848_, 0);
lean_inc(v_fst_2850_);
lean_dec_ref(v_x_2848_);
v_val_2851_ = lean_ctor_get(v_p_2849_, 0);
v___x_2852_ = l_Lean_Syntax_isOfKind(v_fst_2850_, v_val_2851_);
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2853_, lean_object* v_x_2854_, lean_object* v_p_2855_){
_start:
{
uint8_t v___x_123__boxed_2856_; uint8_t v_res_2857_; lean_object* v_r_2858_; 
v___x_123__boxed_2856_ = lean_unbox(v___x_2853_);
v_res_2857_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2856_, v_x_2854_, v_p_2855_);
lean_dec(v_p_2855_);
v_r_2858_ = lean_box(v_res_2857_);
return v_r_2858_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2859_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
uint8_t v___x_2860_; 
v___x_2860_ = 1;
return v___x_2860_;
}
else
{
lean_object* v_head_2861_; uint8_t v___x_2862_; 
v_head_2861_ = lean_ctor_get(v_x_2859_, 0);
v___x_2862_ = lean_unbox(v_head_2861_);
if (v___x_2862_ == 0)
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_unbox(v_head_2861_);
return v___x_2863_;
}
else
{
lean_object* v_tail_2864_; 
v_tail_2864_ = lean_ctor_get(v_x_2859_, 1);
v_x_2859_ = v_tail_2864_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2866_);
lean_dec(v_x_2866_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2871_, lean_object* v_pattern_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = l_List_lengthTR___redArg(v_pattern_2872_);
v___x_2874_ = l_List_lengthTR___redArg(v_stack_2871_);
v___x_2875_ = lean_nat_dec_le(v___x_2873_, v___x_2874_);
lean_dec(v___x_2874_);
lean_dec(v___x_2873_);
if (v___x_2875_ == 0)
{
lean_dec(v_pattern_2872_);
lean_dec(v_stack_2871_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v___f_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2876_ = lean_box(v___x_2875_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2877_, 0, v___x_2876_);
v___x_2878_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2879_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2877_, v_stack_2871_, v_pattern_2872_, v___x_2878_);
v___x_2880_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2879_);
lean_dec(v___x_2879_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2881_, lean_object* v_pattern_2882_){
_start:
{
uint8_t v_res_2883_; lean_object* v_r_2884_; 
v_res_2883_ = l_Lean_Syntax_Stack_matches(v_stack_2881_, v_pattern_2882_);
v_r_2884_ = lean_box(v_res_2883_);
return v_r_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2885_, lean_object* v_trailing_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2885_);
if (lean_obj_tag(v___x_2887_) == 1)
{
lean_object* v_val_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2923_; 
v_val_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2923_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_val_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2923_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
if (lean_obj_tag(v_val_2888_) == 0)
{
lean_object* v_trailing_2892_; lean_object* v_leading_2893_; lean_object* v_pos_2894_; lean_object* v_endPos_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2921_; 
v_trailing_2892_ = lean_ctor_get(v_val_2888_, 2);
v_leading_2893_ = lean_ctor_get(v_val_2888_, 0);
v_pos_2894_ = lean_ctor_get(v_val_2888_, 1);
v_endPos_2895_ = lean_ctor_get(v_val_2888_, 3);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_val_2888_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2897_ = v_val_2888_;
v_isShared_2898_ = v_isSharedCheck_2921_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_endPos_2895_);
lean_inc(v_trailing_2892_);
lean_inc(v_pos_2894_);
lean_inc(v_leading_2893_);
lean_dec(v_val_2888_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2921_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_str_2899_; lean_object* v_startPos_2900_; lean_object* v_stopPos_2901_; lean_object* v_startPos_2902_; lean_object* v_stopPos_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2919_; 
v_str_2899_ = lean_ctor_get(v_trailing_2892_, 0);
lean_inc_ref(v_str_2899_);
v_startPos_2900_ = lean_ctor_get(v_trailing_2892_, 1);
lean_inc(v_startPos_2900_);
v_stopPos_2901_ = lean_ctor_get(v_trailing_2892_, 2);
lean_inc(v_stopPos_2901_);
lean_dec_ref(v_trailing_2892_);
v_startPos_2902_ = lean_ctor_get(v_trailing_2886_, 1);
v_stopPos_2903_ = lean_ctor_get(v_trailing_2886_, 2);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_trailing_2886_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_trailing_2886_, 0);
lean_dec(v_unused_2920_);
v___x_2905_ = v_trailing_2886_;
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_stopPos_2903_);
lean_inc(v_startPos_2902_);
lean_dec(v_trailing_2886_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
uint8_t v_decide_2907_; 
v_decide_2907_ = lean_nat_dec_eq(v_stopPos_2901_, v_startPos_2902_);
lean_dec(v_startPos_2902_);
lean_dec(v_stopPos_2901_);
if (v_decide_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_del_object(v___x_2905_);
lean_dec(v_stopPos_2903_);
lean_dec(v_startPos_2900_);
lean_dec_ref(v_str_2899_);
lean_del_object(v___x_2897_);
lean_dec(v_endPos_2895_);
lean_dec(v_pos_2894_);
lean_dec_ref(v_leading_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_stx_2885_);
v___x_2908_ = lean_box(0);
return v___x_2908_;
}
else
{
lean_object* v_trailing_2910_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v_startPos_2900_);
lean_ctor_set(v___x_2905_, 0, v_str_2899_);
v_trailing_2910_ = v___x_2905_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_str_2899_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_startPos_2900_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_stopPos_2903_);
v_trailing_2910_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2912_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 2, v_trailing_2910_);
v___x_2912_ = v___x_2897_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_leading_2893_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_pos_2894_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_trailing_2910_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_endPos_2895_);
v___x_2912_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2913_ = l_Lean_Syntax_setTailInfo(v_stx_2885_, v___x_2912_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2913_);
v___x_2915_ = v___x_2890_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2922_; 
lean_del_object(v___x_2890_);
lean_dec(v_val_2888_);
lean_dec_ref(v_trailing_2886_);
lean_dec(v_stx_2885_);
v___x_2922_ = lean_box(0);
return v___x_2922_;
}
}
}
else
{
lean_object* v___x_2924_; 
lean_dec(v___x_2887_);
lean_dec_ref(v_trailing_2886_);
lean_dec(v_stx_2885_);
v___x_2924_ = lean_box(0);
return v___x_2924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2925_, lean_object* v_trailing_2926_){
_start:
{
lean_object* v___x_2927_; 
lean_inc(v_stx_2925_);
v___x_2927_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2925_, v_trailing_2926_);
if (lean_obj_tag(v___x_2927_) == 0)
{
return v_stx_2925_;
}
else
{
lean_object* v_val_2928_; 
lean_dec(v_stx_2925_);
v_val_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v___x_2927_, 1);
return v_val_2928_;
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

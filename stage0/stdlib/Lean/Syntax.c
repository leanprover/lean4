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
lean_dec_ref_known(v_x_1126_, 4);
lean_dec(v_info_1147_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___lam__0(lean_object* v_fst_1352_, lean_object* v_snd_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_fst_1352_);
lean_ctor_set(v___x_1354_, 1, v_snd_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
return v_x_1355_;
}
else
{
lean_object* v_head_1357_; lean_object* v_tail_1358_; lean_object* v_startPos_1359_; lean_object* v_stopPos_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_head_1357_ = lean_ctor_get(v_x_1356_, 0);
v_tail_1358_ = lean_ctor_get(v_x_1356_, 1);
v_startPos_1359_ = lean_ctor_get(v_head_1357_, 1);
v_stopPos_1360_ = lean_ctor_get(v_head_1357_, 2);
v___x_1361_ = lean_nat_sub(v_stopPos_1360_, v_startPos_1359_);
v___x_1362_ = lean_nat_add(v_x_1355_, v___x_1361_);
lean_dec(v___x_1361_);
lean_dec(v_x_1355_);
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = lean_nat_add(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
v_x_1355_ = v___x_1364_;
v_x_1356_ = v_tail_1358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1366_, v_x_1367_);
lean_dec(v_x_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1373_, lean_object* v_pos_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
if (lean_obj_tag(v_a_1375_) == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = l_List_reverse___redArg(v_a_1376_);
return v___x_1377_;
}
else
{
lean_object* v_head_1378_; lean_object* v_tail_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1397_; 
v_head_1378_ = lean_ctor_get(v_a_1375_, 0);
v_tail_1379_ = lean_ctor_get(v_a_1375_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_a_1375_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1381_ = v_a_1375_;
v_isShared_1382_ = v_isSharedCheck_1397_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_tail_1379_);
lean_inc(v_head_1378_);
lean_dec(v_a_1375_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1397_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_stopPos_1383_; lean_object* v_startPos_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_info_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v_stopPos_1383_ = lean_ctor_get(v_head_1378_, 2);
lean_inc(v_stopPos_1383_);
lean_dec(v_head_1378_);
v_startPos_1384_ = lean_ctor_get(v_rawVal_1373_, 1);
v___x_1385_ = lean_nat_sub(v_stopPos_1383_, v_startPos_1384_);
lean_dec(v_stopPos_1383_);
v___x_1386_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1387_ = lean_nat_add(v___x_1385_, v_pos_1374_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_nat_add(v___x_1388_, v___x_1387_);
v_info_1390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1390_, 0, v___x_1386_);
lean_ctor_set(v_info_1390_, 1, v___x_1387_);
lean_ctor_set(v_info_1390_, 2, v___x_1386_);
lean_ctor_set(v_info_1390_, 3, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_info_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v_a_1376_);
lean_ctor_set(v___x_1381_, 0, v___x_1392_);
v___x_1394_ = v___x_1381_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_a_1376_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v_a_1375_ = v_tail_1379_;
v_a_1376_ = v___x_1394_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1398_, lean_object* v_pos_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1398_, v_pos_1399_, v_a_1400_, v_a_1401_);
lean_dec(v_pos_1399_);
lean_dec_ref(v_rawVal_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1403_, lean_object* v_pos_1404_, lean_object* v_trailing_1405_, lean_object* v_leading_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
if (lean_obj_tag(v_a_1407_) == 0)
{
lean_object* v___x_1409_; 
lean_dec_ref(v_leading_1406_);
lean_dec_ref(v_trailing_1405_);
v___x_1409_ = l_List_reverse___redArg(v_a_1408_);
return v___x_1409_;
}
else
{
lean_object* v_head_1410_; lean_object* v_snd_1411_; lean_object* v_tail_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1442_; 
v_head_1410_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_head_1410_);
v_snd_1411_ = lean_ctor_get(v_head_1410_, 1);
lean_inc(v_snd_1411_);
v_tail_1412_ = lean_ctor_get(v_a_1407_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_a_1407_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_a_1407_, 0);
lean_dec(v_unused_1443_);
v___x_1414_ = v_a_1407_;
v_isShared_1415_ = v_isSharedCheck_1442_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_tail_1412_);
lean_dec(v_a_1407_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1442_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_fst_1416_; lean_object* v_startPos_1417_; lean_object* v_stopPos_1418_; lean_object* v_startPos_1419_; lean_object* v_stopPos_1420_; lean_object* v_off_1421_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1436_; lean_object* v___x_1439_; uint8_t v_decide_1440_; 
v_fst_1416_ = lean_ctor_get(v_head_1410_, 0);
lean_inc(v_fst_1416_);
lean_dec(v_head_1410_);
v_startPos_1417_ = lean_ctor_get(v_snd_1411_, 1);
v_stopPos_1418_ = lean_ctor_get(v_snd_1411_, 2);
v_startPos_1419_ = lean_ctor_get(v_rawVal_1403_, 1);
v_stopPos_1420_ = lean_ctor_get(v_rawVal_1403_, 2);
v_off_1421_ = lean_nat_sub(v_startPos_1417_, v_startPos_1419_);
v___x_1439_ = lean_unsigned_to_nat(0u);
v_decide_1440_ = lean_nat_dec_eq(v_off_1421_, v___x_1439_);
if (v_decide_1440_ == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1436_ = v___x_1441_;
goto v___jp_1435_;
}
else
{
lean_inc_ref(v_leading_1406_);
v___y_1436_ = v_leading_1406_;
goto v___jp_1435_;
}
v___jp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_info_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1425_ = lean_nat_add(v_off_1421_, v_pos_1404_);
lean_dec(v_off_1421_);
v___x_1426_ = lean_nat_sub(v_stopPos_1418_, v_startPos_1417_);
v___x_1427_ = lean_nat_add(v___x_1426_, v___x_1425_);
lean_dec(v___x_1426_);
v_info_1428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1428_, 0, v___y_1423_);
lean_ctor_set(v_info_1428_, 1, v___x_1425_);
lean_ctor_set(v_info_1428_, 2, v___y_1424_);
lean_ctor_set(v_info_1428_, 3, v___x_1427_);
v___x_1429_ = lean_box(0);
v___x_1430_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1430_, 0, v_info_1428_);
lean_ctor_set(v___x_1430_, 1, v_snd_1411_);
lean_ctor_set(v___x_1430_, 2, v_fst_1416_);
lean_ctor_set(v___x_1430_, 3, v___x_1429_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_a_1408_);
lean_ctor_set(v___x_1414_, 0, v___x_1430_);
v___x_1432_ = v___x_1414_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1408_);
v___x_1432_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v_a_1407_ = v_tail_1412_;
v_a_1408_ = v___x_1432_;
goto _start;
}
}
v___jp_1435_:
{
uint8_t v_decide_1437_; 
v_decide_1437_ = lean_nat_dec_eq(v_stopPos_1418_, v_stopPos_1420_);
if (v_decide_1437_ == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1423_ = v___y_1436_;
v___y_1424_ = v___x_1438_;
goto v___jp_1422_;
}
else
{
lean_inc_ref(v_trailing_1405_);
v___y_1423_ = v___y_1436_;
v___y_1424_ = v_trailing_1405_;
goto v___jp_1422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1444_, lean_object* v_pos_1445_, lean_object* v_trailing_1446_, lean_object* v_leading_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1444_, v_pos_1445_, v_trailing_1446_, v_leading_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_pos_1445_);
lean_dec_ref(v_rawVal_1444_);
return v_res_1450_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__6(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1459_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__5));
v___x_1460_ = lean_unsigned_to_nat(9u);
v___x_1461_ = lean_unsigned_to_nat(358u);
v___x_1462_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1463_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1464_ = l_mkPanicMessageWithDecl(v___x_1463_, v___x_1462_, v___x_1461_, v___x_1460_, v___x_1459_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1465_, lean_object* v_nFields_x3f_1466_){
_start:
{
if (lean_obj_tag(v_stx_1465_) == 3)
{
lean_object* v_info_1467_; 
v_info_1467_ = lean_ctor_get(v_stx_1465_, 0);
lean_inc(v_info_1467_);
if (lean_obj_tag(v_info_1467_) == 0)
{
lean_object* v_rawVal_1468_; lean_object* v_val_1469_; lean_object* v_leading_1470_; lean_object* v_pos_1471_; lean_object* v_trailing_1472_; lean_object* v_rawComps_1473_; uint8_t v___x_1474_; 
v_rawVal_1468_ = lean_ctor_get(v_stx_1465_, 1);
lean_inc_ref_n(v_rawVal_1468_, 2);
v_val_1469_ = lean_ctor_get(v_stx_1465_, 2);
lean_inc(v_val_1469_);
lean_dec_ref_known(v_stx_1465_, 4);
v_leading_1470_ = lean_ctor_get(v_info_1467_, 0);
lean_inc_ref(v_leading_1470_);
v_pos_1471_ = lean_ctor_get(v_info_1467_, 1);
lean_inc(v_pos_1471_);
v_trailing_1472_ = lean_ctor_get(v_info_1467_, 2);
lean_inc_ref(v_trailing_1472_);
lean_dec_ref_known(v_info_1467_, 4);
v_rawComps_1473_ = l_Lean_Syntax_splitNameLit(v_rawVal_1468_);
v___x_1474_ = l_List_isEmpty___redArg(v_rawComps_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___f_1475_; lean_object* v_val_1476_; lean_object* v_nameComps_1477_; lean_object* v___y_1479_; 
v___f_1475_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
v_val_1476_ = l_Lean_Name_eraseMacroScopes(v_val_1469_);
lean_dec(v_val_1469_);
v_nameComps_1477_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1476_, v_nFields_x3f_1466_);
if (lean_obj_tag(v_nFields_x3f_1466_) == 1)
{
lean_object* v_val_1494_; lean_object* v_str_1495_; lean_object* v_startPos_1496_; lean_object* v_stopPos_1497_; lean_object* v___x_1498_; lean_object* v_nPrefix_1499_; lean_object* v___y_1501_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_prefixSz_1507_; lean_object* v___x_1508_; lean_object* v_prefixSz_1509_; lean_object* v___y_1511_; uint8_t v___x_1516_; 
v_val_1494_ = lean_ctor_get(v_nFields_x3f_1466_, 0);
v_str_1495_ = lean_ctor_get(v_rawVal_1468_, 0);
v_startPos_1496_ = lean_ctor_get(v_rawVal_1468_, 1);
v_stopPos_1497_ = lean_ctor_get(v_rawVal_1468_, 2);
v___x_1498_ = l_List_lengthTR___redArg(v_rawComps_1473_);
v_nPrefix_1499_ = lean_nat_sub(v___x_1498_, v_val_1494_);
lean_dec(v___x_1498_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
lean_inc(v_nPrefix_1499_);
lean_inc(v_rawComps_1473_);
v___x_1506_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1473_, v_rawComps_1473_, v_nPrefix_1499_, v___x_1505_);
v_prefixSz_1507_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1504_, v___x_1506_);
lean_dec(v___x_1506_);
v___x_1508_ = lean_unsigned_to_nat(1u);
v_prefixSz_1509_ = lean_nat_sub(v_prefixSz_1507_, v___x_1508_);
lean_dec(v_prefixSz_1507_);
v___x_1516_ = lean_nat_dec_le(v_prefixSz_1509_, v___x_1504_);
if (v___x_1516_ == 0)
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_nat_dec_le(v_stopPos_1497_, v_startPos_1496_);
if (v___x_1517_ == 0)
{
lean_inc(v_startPos_1496_);
v___y_1511_ = v_startPos_1496_;
goto v___jp_1510_;
}
else
{
lean_inc(v_stopPos_1497_);
v___y_1511_ = v_stopPos_1497_;
goto v___jp_1510_;
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_prefixSz_1509_);
v___x_1518_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1501_ = v___x_1518_;
goto v___jp_1500_;
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_List_drop___redArg(v_nPrefix_1499_, v_rawComps_1473_);
lean_dec(v_rawComps_1473_);
v___x_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___y_1479_ = v___x_1503_;
goto v___jp_1478_;
}
v___jp_1510_:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_nat_add(v_startPos_1496_, v_prefixSz_1509_);
lean_dec(v_prefixSz_1509_);
v___x_1513_ = lean_nat_dec_le(v_stopPos_1497_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
lean_inc_ref(v_str_1495_);
v___x_1514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1514_, 0, v_str_1495_);
lean_ctor_set(v___x_1514_, 1, v___y_1511_);
lean_ctor_set(v___x_1514_, 2, v___x_1512_);
v___y_1501_ = v___x_1514_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v___x_1512_);
lean_inc(v_stopPos_1497_);
lean_inc_ref(v_str_1495_);
v___x_1515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1515_, 0, v_str_1495_);
lean_ctor_set(v___x_1515_, 1, v___y_1511_);
lean_ctor_set(v___x_1515_, 2, v_stopPos_1497_);
v___y_1501_ = v___x_1515_;
goto v___jp_1500_;
}
}
}
else
{
v___y_1479_ = v_rawComps_1473_;
goto v___jp_1478_;
}
v___jp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = l_List_lengthTR___redArg(v_nameComps_1477_);
v___x_1481_ = l_List_lengthTR___redArg(v___y_1479_);
v___x_1482_ = lean_nat_dec_eq(v___x_1480_, v___x_1481_);
lean_dec(v___x_1481_);
lean_dec(v___x_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
lean_dec(v___y_1479_);
lean_dec(v_nameComps_1477_);
lean_dec_ref(v_trailing_1472_);
lean_dec(v_pos_1471_);
lean_dec_ref(v_leading_1470_);
lean_dec_ref(v_rawVal_1468_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_comps_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_seps_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1484_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
lean_inc(v___y_1479_);
v___x_1485_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_1475_, v_nameComps_1477_, v___y_1479_, v___x_1484_);
v___x_1486_ = lean_box(0);
v_comps_1487_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1468_, v_pos_1471_, v_trailing_1472_, v_leading_1470_, v___x_1485_, v___x_1486_);
v___x_1488_ = lean_array_mk(v___y_1479_);
v___x_1489_ = lean_array_pop(v___x_1488_);
v___x_1490_ = lean_array_to_list(v___x_1489_);
v_seps_1491_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1468_, v_pos_1471_, v___x_1490_, v___x_1486_);
lean_dec(v_pos_1471_);
lean_dec_ref(v_rawVal_1468_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_comps_1487_);
lean_ctor_set(v___x_1492_, 1, v_seps_1491_);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
}
else
{
lean_object* v___x_1519_; 
lean_dec(v_rawComps_1473_);
lean_dec_ref(v_trailing_1472_);
lean_dec(v_pos_1471_);
lean_dec_ref(v_leading_1470_);
lean_dec(v_val_1469_);
lean_dec_ref(v_rawVal_1468_);
v___x_1519_ = lean_box(0);
return v___x_1519_;
}
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref_known(v_stx_1465_, 4);
lean_dec(v_info_1467_);
v___x_1520_ = lean_box(0);
return v___x_1520_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_stx_1465_);
v___x_1521_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__6, &l_Lean_Syntax_identComponents_x3f___closed__6_once, _init_l_Lean_Syntax_identComponents_x3f___closed__6);
v___x_1522_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1521_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1523_, lean_object* v_nFields_x3f_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Syntax_identComponents_x3f(v_stx_1523_, v_nFields_x3f_1524_);
lean_dec(v_nFields_x3f_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1526_, lean_object* v_nFields_x3f_1527_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1527_) == 1)
{
lean_object* v_val_1528_; lean_object* v_nameComps_1529_; lean_object* v___x_1530_; lean_object* v_nPrefix_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_namePrefix_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_val_1528_ = lean_ctor_get(v_nFields_x3f_1527_, 0);
v_nameComps_1529_ = l_Lean_Name_components(v_n_1526_);
v___x_1530_ = l_List_lengthTR___redArg(v_nameComps_1529_);
v_nPrefix_1531_ = lean_nat_sub(v___x_1530_, v_val_1528_);
lean_dec(v___x_1530_);
v___x_1532_ = lean_box(0);
v___x_1533_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1531_);
lean_inc(v_nameComps_1529_);
v___x_1534_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1529_, v_nameComps_1529_, v_nPrefix_1531_, v___x_1533_);
v_namePrefix_1535_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1532_, v___x_1534_);
v___x_1536_ = l_List_drop___redArg(v_nPrefix_1531_, v_nameComps_1529_);
lean_dec(v_nameComps_1529_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_namePrefix_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Name_components(v_n_1526_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1539_, lean_object* v_nFields_x3f_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1539_, v_nFields_x3f_1540_);
lean_dec(v_nFields_x3f_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_panic_fn_borrowed(v___x_1543_, v_msg_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
if (lean_obj_tag(v_a_1546_) == 0)
{
lean_object* v___x_1548_; 
lean_dec(v_info_1545_);
v___x_1548_ = l_List_reverse___redArg(v_a_1547_);
return v___x_1548_;
}
else
{
lean_object* v_head_1549_; lean_object* v_tail_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1565_; 
v_head_1549_ = lean_ctor_get(v_a_1546_, 0);
v_tail_1550_ = lean_ctor_get(v_a_1546_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_a_1546_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1552_ = v_a_1546_;
v_isShared_1553_ = v_isSharedCheck_1565_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_tail_1550_);
lean_inc(v_head_1549_);
lean_dec(v_a_1546_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1565_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1554_ = 1;
lean_inc(v_head_1549_);
v___x_1555_ = l_Lean_Name_toString(v_head_1549_, v___x_1554_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_string_utf8_byte_size(v___x_1555_);
v___x_1558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1555_);
lean_ctor_set(v___x_1558_, 1, v___x_1556_);
lean_ctor_set(v___x_1558_, 2, v___x_1557_);
v___x_1559_ = lean_box(0);
lean_inc(v_info_1545_);
v___x_1560_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1560_, 0, v_info_1545_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
lean_ctor_set(v___x_1560_, 2, v_head_1549_);
lean_ctor_set(v___x_1560_, 3, v___x_1559_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v_a_1547_);
lean_ctor_set(v___x_1552_, 0, v___x_1560_);
v___x_1562_ = v___x_1552_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_a_1547_);
v___x_1562_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v_a_1546_ = v_tail_1550_;
v_a_1547_ = v___x_1562_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__5));
v___x_1568_ = lean_unsigned_to_nat(9u);
v___x_1569_ = lean_unsigned_to_nat(393u);
v___x_1570_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1571_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1572_ = l_mkPanicMessageWithDecl(v___x_1571_, v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1573_, lean_object* v_nFields_x3f_1574_){
_start:
{
if (lean_obj_tag(v_stx_1573_) == 3)
{
lean_object* v_info_1575_; lean_object* v_rawVal_1576_; lean_object* v_val_1577_; lean_object* v_val_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_info_1575_ = lean_ctor_get(v_stx_1573_, 0);
lean_inc(v_info_1575_);
v_rawVal_1576_ = lean_ctor_get(v_stx_1573_, 1);
v_val_1577_ = lean_ctor_get(v_stx_1573_, 2);
v_val_1578_ = l_Lean_Name_eraseMacroScopes(v_val_1577_);
v___x_1579_ = l_Lean_Name_getNumParts(v_val_1578_);
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = lean_nat_dec_le(v___x_1579_, v___x_1580_);
lean_dec(v___x_1579_);
if (v___x_1581_ == 0)
{
if (lean_obj_tag(v_info_1575_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Syntax_identComponents_x3f(v_stx_1573_, v_nFields_x3f_1574_);
if (lean_obj_tag(v___x_1582_) == 1)
{
lean_object* v_val_1583_; lean_object* v_fst_1584_; 
lean_dec_ref_known(v_info_1575_, 4);
lean_dec(v_val_1578_);
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_fst_1584_ = lean_ctor_get(v_val_1583_, 0);
lean_inc(v_fst_1584_);
lean_dec(v_val_1583_);
return v_fst_1584_;
}
else
{
lean_object* v_nameComps_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v___x_1582_);
v_nameComps_1585_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1578_, v_nFields_x3f_1574_);
v___x_1586_ = lean_box(0);
v___x_1587_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1575_, v_nameComps_1585_, v___x_1586_);
return v___x_1587_;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref_known(v_stx_1573_, 4);
v___x_1588_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1578_, v_nFields_x3f_1574_);
v___x_1589_ = lean_box(0);
v___x_1590_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1575_, v___x_1588_, v___x_1589_);
return v___x_1590_;
}
}
else
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1599_; 
lean_inc_ref(v_rawVal_1576_);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_stx_1573_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; lean_object* v_unused_1603_; 
v_unused_1600_ = lean_ctor_get(v_stx_1573_, 3);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_stx_1573_, 2);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_stx_1573_, 1);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_stx_1573_, 0);
lean_dec(v_unused_1603_);
v___x_1592_ = v_stx_1573_;
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_stx_1573_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 3, v___x_1594_);
lean_ctor_set(v___x_1592_, 2, v_val_1578_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_info_1575_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_rawVal_1576_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_val_1578_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v___x_1594_);
return v___x_1597_;
}
}
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_stx_1573_);
v___x_1604_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1605_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1604_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1606_, lean_object* v_nFields_x3f_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Syntax_identComponents(v_stx_1606_, v_nFields_x3f_1607_);
lean_dec(v_nFields_x3f_1607_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1609_, uint8_t v_firstChoiceOnly_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1611_, 0, v_stx_1609_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*1, v_firstChoiceOnly_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1612_, lean_object* v_firstChoiceOnly_1613_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1614_; lean_object* v_res_1615_; 
v_firstChoiceOnly_boxed_1614_ = lean_unbox(v_firstChoiceOnly_1613_);
v_res_1615_ = l_Lean_Syntax_topDown(v_stx_1612_, v_firstChoiceOnly_boxed_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1616_, lean_object* v_____r_1617_, lean_object* v_b_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_b_1618_);
v___x_1620_ = lean_apply_2(v_toPure_1616_, lean_box(0), v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1621_, lean_object* v_toPure_1622_, lean_object* v_____s_1623_){
_start:
{
lean_object* v_fst_1624_; 
v_fst_1624_ = lean_ctor_get(v_____s_1623_, 0);
if (lean_obj_tag(v_fst_1624_) == 0)
{
lean_object* v_snd_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_toPure_1622_);
v_snd_1625_ = lean_ctor_get(v_____s_1623_, 1);
lean_inc(v_snd_1625_);
lean_dec_ref(v_____s_1623_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_apply_2(v___f_1621_, v___x_1626_, v_snd_1625_);
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1629_; 
lean_inc_ref(v_fst_1624_);
lean_dec_ref(v_____s_1623_);
lean_dec(v___f_1621_);
v_val_1628_ = lean_ctor_get(v_fst_1624_, 0);
lean_inc(v_val_1628_);
lean_dec_ref_known(v_fst_1624_, 1);
v___x_1629_ = lean_apply_2(v_toPure_1622_, lean_box(0), v_val_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1630_, lean_object* v_toPure_1631_, lean_object* v___x_1632_, lean_object* v_____do__lift_1633_){
_start:
{
if (lean_obj_tag(v_____do__lift_1633_) == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_____do__lift_1633_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v_snd_1630_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
v___x_1637_ = lean_apply_2(v_toPure_1631_, lean_box(0), v___x_1636_);
return v___x_1637_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_snd_1630_);
v_a_1638_ = lean_ctor_get(v_____do__lift_1633_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_____do__lift_1633_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1640_ = v_____do__lift_1633_;
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v_____do__lift_1633_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1632_);
lean_ctor_set(v___x_1642_, 1, v_a_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_apply_2(v_toPure_1631_, lean_box(0), v___x_1644_);
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1648_, lean_object* v___x_1649_, lean_object* v_inst_1650_, lean_object* v_f_1651_, lean_object* v_firstChoiceOnly_1652_, lean_object* v_toBind_1653_, lean_object* v_a_1654_, lean_object* v_x_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1657_; lean_object* v_res_1658_; 
v_firstChoiceOnly_boxed_1657_ = lean_unbox(v_firstChoiceOnly_1652_);
v_res_1658_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1648_, v___x_1649_, v_inst_1650_, v_f_1651_, v_firstChoiceOnly_boxed_1657_, v_toBind_1653_, v_a_1654_, v_x_1655_, v___y_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1662_, lean_object* v_stx_1663_, lean_object* v_inst_1664_, lean_object* v_f_1665_, uint8_t v_firstChoiceOnly_1666_, lean_object* v_toBind_1667_, lean_object* v___f_1668_, lean_object* v___x_1669_, lean_object* v___f_1670_, lean_object* v_____do__lift_1671_){
_start:
{
if (lean_obj_tag(v_____do__lift_1671_) == 0)
{
lean_object* v___x_1672_; 
lean_dec(v___f_1670_);
lean_dec(v___f_1668_);
lean_dec(v_toBind_1667_);
lean_dec(v_f_1665_);
lean_dec_ref(v_inst_1664_);
lean_dec(v_stx_1663_);
v___x_1672_ = lean_apply_2(v_toPure_1662_, lean_box(0), v_____do__lift_1671_);
return v___x_1672_;
}
else
{
if (lean_obj_tag(v_stx_1663_) == 1)
{
lean_object* v_a_1673_; lean_object* v_kind_1674_; lean_object* v_args_1675_; 
lean_dec(v___f_1670_);
v_a_1673_ = lean_ctor_get(v_____do__lift_1671_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v_____do__lift_1671_, 1);
v_kind_1674_ = lean_ctor_get(v_stx_1663_, 1);
lean_inc(v_kind_1674_);
v_args_1675_ = lean_ctor_get(v_stx_1663_, 2);
lean_inc_ref(v_args_1675_);
lean_dec_ref_known(v_stx_1663_, 3);
if (v_firstChoiceOnly_1666_ == 0)
{
lean_dec(v_kind_1674_);
goto v___jp_1676_;
}
else
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1686_ = lean_name_eq(v_kind_1674_, v___x_1685_);
lean_dec(v_kind_1674_);
if (v___x_1686_ == 0)
{
goto v___jp_1676_;
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec(v___f_1668_);
lean_dec(v_toBind_1667_);
lean_dec(v_toPure_1662_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = lean_array_get(v___x_1669_, v_args_1675_, v___x_1687_);
lean_dec_ref(v_args_1675_);
v___x_1689_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1664_, v_f_1665_, v_firstChoiceOnly_1666_, v___x_1688_, v_a_1673_);
return v___x_1689_;
}
}
v___jp_1676_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___f_1679_; lean_object* v___x_1680_; size_t v_sz_1681_; size_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_box(v_firstChoiceOnly_1666_);
lean_inc(v_toBind_1667_);
lean_inc_ref(v_inst_1664_);
v___f_1679_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1679_, 0, v_toPure_1662_);
lean_closure_set(v___f_1679_, 1, v___x_1677_);
lean_closure_set(v___f_1679_, 2, v_inst_1664_);
lean_closure_set(v___f_1679_, 3, v_f_1665_);
lean_closure_set(v___f_1679_, 4, v___x_1678_);
lean_closure_set(v___f_1679_, 5, v_toBind_1667_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1677_);
lean_ctor_set(v___x_1680_, 1, v_a_1673_);
v_sz_1681_ = lean_array_size(v_args_1675_);
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1664_, v_args_1675_, v___f_1679_, v_sz_1681_, v___x_1682_, v___x_1680_);
v___x_1684_ = lean_apply_4(v_toBind_1667_, lean_box(0), lean_box(0), v___x_1683_, v___f_1668_);
return v___x_1684_;
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v___f_1668_);
lean_dec(v_toBind_1667_);
lean_dec(v_f_1665_);
lean_dec_ref(v_inst_1664_);
lean_dec(v_stx_1663_);
lean_dec(v_toPure_1662_);
v_a_1690_ = lean_ctor_get(v_____do__lift_1671_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v_____do__lift_1671_, 1);
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_apply_2(v___f_1670_, v___x_1691_, v_a_1690_);
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1693_, lean_object* v_stx_1694_, lean_object* v_inst_1695_, lean_object* v_f_1696_, lean_object* v_firstChoiceOnly_1697_, lean_object* v_toBind_1698_, lean_object* v___f_1699_, lean_object* v___x_1700_, lean_object* v___f_1701_, lean_object* v_____do__lift_1702_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1703_; lean_object* v_res_1704_; 
v_firstChoiceOnly_boxed_1703_ = lean_unbox(v_firstChoiceOnly_1697_);
v_res_1704_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1693_, v_stx_1694_, v_inst_1695_, v_f_1696_, v_firstChoiceOnly_boxed_1703_, v_toBind_1698_, v___f_1699_, v___x_1700_, v___f_1701_, v_____do__lift_1702_);
lean_dec(v___x_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1705_, lean_object* v_f_1706_, uint8_t v_firstChoiceOnly_1707_, lean_object* v_stx_1708_, lean_object* v_b_1709_){
_start:
{
lean_object* v_toApplicative_1710_; lean_object* v_toBind_1711_; lean_object* v_toPure_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; 
v_toApplicative_1710_ = lean_ctor_get(v_inst_1705_, 0);
v_toBind_1711_ = lean_ctor_get(v_inst_1705_, 1);
lean_inc_n(v_toBind_1711_, 2);
v_toPure_1712_ = lean_ctor_get(v_toApplicative_1710_, 1);
lean_inc_n(v_toPure_1712_, 3);
v___x_1713_ = lean_box(0);
lean_inc(v_f_1706_);
lean_inc(v_stx_1708_);
v___x_1714_ = lean_apply_2(v_f_1706_, v_stx_1708_, v_b_1709_);
v___f_1715_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1715_, 0, v_toPure_1712_);
lean_inc_ref(v___f_1715_);
v___f_1716_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1716_, 0, v___f_1715_);
lean_closure_set(v___f_1716_, 1, v_toPure_1712_);
v___x_1717_ = lean_box(v_firstChoiceOnly_1707_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1718_, 0, v_toPure_1712_);
lean_closure_set(v___f_1718_, 1, v_stx_1708_);
lean_closure_set(v___f_1718_, 2, v_inst_1705_);
lean_closure_set(v___f_1718_, 3, v_f_1706_);
lean_closure_set(v___f_1718_, 4, v___x_1717_);
lean_closure_set(v___f_1718_, 5, v_toBind_1711_);
lean_closure_set(v___f_1718_, 6, v___f_1716_);
lean_closure_set(v___f_1718_, 7, v___x_1713_);
lean_closure_set(v___f_1718_, 8, v___f_1715_);
v___x_1719_ = lean_apply_4(v_toBind_1711_, lean_box(0), lean_box(0), v___x_1714_, v___f_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1720_, lean_object* v___x_1721_, lean_object* v_inst_1722_, lean_object* v_f_1723_, uint8_t v_firstChoiceOnly_1724_, lean_object* v_toBind_1725_, lean_object* v_a_1726_, lean_object* v_x_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_snd_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_snd_1729_ = lean_ctor_get(v___y_1728_, 1);
lean_inc_n(v_snd_1729_, 2);
lean_dec_ref(v___y_1728_);
v___f_1730_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1730_, 0, v_snd_1729_);
lean_closure_set(v___f_1730_, 1, v_toPure_1720_);
lean_closure_set(v___f_1730_, 2, v___x_1721_);
v___x_1731_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1722_, v_f_1723_, v_firstChoiceOnly_1724_, v_a_1726_, v_snd_1729_);
v___x_1732_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1731_, v___f_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1733_, lean_object* v_f_1734_, lean_object* v_firstChoiceOnly_1735_, lean_object* v_stx_1736_, lean_object* v_b_1737_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1738_; lean_object* v_res_1739_; 
v_firstChoiceOnly_boxed_1738_ = lean_unbox(v_firstChoiceOnly_1735_);
v_res_1739_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1733_, v_f_1734_, v_firstChoiceOnly_boxed_1738_, v_stx_1736_, v_b_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1740_, lean_object* v_inst_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_f_1743_, uint8_t v_firstChoiceOnly_1744_, lean_object* v_stx_1745_, lean_object* v_b_1746_, lean_object* v_inst_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1741_, v_f_1743_, v_firstChoiceOnly_1744_, v_stx_1745_, v_b_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1749_, lean_object* v_inst_1750_, lean_object* v_00_u03b2_1751_, lean_object* v_f_1752_, lean_object* v_firstChoiceOnly_1753_, lean_object* v_stx_1754_, lean_object* v_b_1755_, lean_object* v_inst_1756_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1757_; lean_object* v_res_1758_; 
v_firstChoiceOnly_boxed_1757_ = lean_unbox(v_firstChoiceOnly_1753_);
v_res_1758_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1749_, v_inst_1750_, v_00_u03b2_1751_, v_f_1752_, v_firstChoiceOnly_boxed_1757_, v_stx_1754_, v_b_1755_, v_inst_1756_);
lean_dec(v_inst_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1759_, lean_object* v_____do__lift_1760_){
_start:
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v_____do__lift_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v_____do__lift_1760_);
v___x_1762_ = lean_apply_2(v_toPure_1759_, lean_box(0), v_a_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1763_, lean_object* v_toBind_1764_, lean_object* v___f_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_x_1767_, lean_object* v_init_1768_, lean_object* v_f_1769_){
_start:
{
uint8_t v_firstChoiceOnly_1770_; lean_object* v_stx_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_firstChoiceOnly_1770_ = lean_ctor_get_uint8(v_x_1767_, sizeof(void*)*1);
v_stx_1771_ = lean_ctor_get(v_x_1767_, 0);
lean_inc(v_stx_1771_);
lean_dec_ref(v_x_1767_);
v___x_1772_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1763_, v_f_1769_, v_firstChoiceOnly_1770_, v_stx_1771_, v_init_1768_);
v___x_1773_ = lean_apply_4(v_toBind_1764_, lean_box(0), lean_box(0), v___x_1772_, v___f_1765_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1774_){
_start:
{
lean_object* v_toApplicative_1775_; lean_object* v_toBind_1776_; lean_object* v_toPure_1777_; lean_object* v___f_1778_; lean_object* v___f_1779_; 
v_toApplicative_1775_ = lean_ctor_get(v_inst_1774_, 0);
v_toBind_1776_ = lean_ctor_get(v_inst_1774_, 1);
lean_inc(v_toBind_1776_);
v_toPure_1777_ = lean_ctor_get(v_toApplicative_1775_, 1);
lean_inc(v_toPure_1777_);
v___f_1778_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1778_, 0, v_toPure_1777_);
v___f_1779_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1779_, 0, v_inst_1774_);
lean_closure_set(v___f_1779_, 1, v_toBind_1776_);
lean_closure_set(v___f_1779_, 2, v___f_1778_);
return v___f_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1780_, lean_object* v_inst_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1784_, lean_object* v_val_1785_){
_start:
{
if (lean_obj_tag(v_info_1784_) == 0)
{
lean_object* v_leading_1786_; lean_object* v_trailing_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_leading_1786_ = lean_ctor_get(v_info_1784_, 0);
lean_inc_ref(v_leading_1786_);
v_trailing_1787_ = lean_ctor_get(v_info_1784_, 2);
lean_inc_ref(v_trailing_1787_);
lean_dec_ref_known(v_info_1784_, 4);
v___x_1788_ = lean_substring_tostring(v_leading_1786_);
v___x_1789_ = lean_string_append(v___x_1788_, v_val_1785_);
v___x_1790_ = lean_substring_tostring(v_trailing_1787_);
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
lean_dec_ref(v___x_1790_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v_info_1784_);
v___x_1792_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1793_ = lean_string_append(v___x_1792_, v_val_1785_);
v___x_1794_ = lean_string_append(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1795_, lean_object* v_val_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1795_, v_val_1796_);
lean_dec_ref(v_val_1796_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1798_, lean_object* v_as_1799_, size_t v_sz_1800_, size_t v_i_1801_, lean_object* v_b_1802_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_lt(v_i_1801_, v_sz_1800_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_b_1802_);
return v___x_1804_;
}
else
{
lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1832_; 
v_snd_1805_ = lean_ctor_get(v_b_1802_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_b_1802_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v_b_1802_, 0);
lean_dec(v_unused_1833_);
v___x_1807_ = v_b_1802_;
v_isShared_1808_ = v_isSharedCheck_1832_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_dec(v_b_1802_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1832_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_array_uget_borrowed(v_as_1799_, v_i_1801_);
lean_inc(v_snd_1805_);
lean_inc(v_a_1809_);
v___x_1810_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1798_, v_a_1809_, v_snd_1805_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; 
lean_del_object(v___x_1807_);
lean_dec(v_snd_1805_);
v___x_1811_ = lean_box(0);
return v___x_1811_;
}
else
{
lean_object* v_val_1812_; 
v_val_1812_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_val_1812_);
if (lean_obj_tag(v_val_1812_) == 0)
{
lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1822_; 
v_isSharedCheck_1822_ = !lean_is_exclusive(v_val_1812_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_val_1812_, 0);
lean_dec(v_unused_1823_);
v___x_1814_ = v_val_1812_;
v_isShared_1815_ = v_isSharedCheck_1822_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v_val_1812_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1822_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1817_ = v___x_1807_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_snd_1805_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
lean_ctor_set(v___x_1814_, 0, v___x_1817_);
v___x_1819_ = v___x_1814_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_dec_ref_known(v___x_1810_, 1);
lean_dec(v_snd_1805_);
v_a_1824_ = lean_ctor_get(v_val_1812_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v_val_1812_, 1);
v___x_1825_ = lean_box(0);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v_a_1824_);
lean_ctor_set(v___x_1807_, 0, v___x_1825_);
v___x_1827_ = v___x_1807_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_a_1824_);
v___x_1827_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
size_t v___x_1828_; size_t v___x_1829_; 
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1801_, v___x_1828_);
v_i_1801_ = v___x_1829_;
v_b_1802_ = v___x_1827_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1834_, lean_object* v_a_1835_, lean_object* v_b_1836_){
_start:
{
lean_object* v_array_1837_; lean_object* v_start_1838_; lean_object* v_stop_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1858_; 
v_array_1837_ = lean_ctor_get(v_a_1835_, 0);
v_start_1838_ = lean_ctor_get(v_a_1835_, 1);
v_stop_1839_ = lean_ctor_get(v_a_1835_, 2);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1841_ = v_a_1835_;
v_isShared_1842_ = v_isSharedCheck_1858_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_stop_1839_);
lean_inc(v_start_1838_);
lean_inc(v_array_1837_);
lean_dec(v_a_1835_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1858_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_lt(v_start_1838_, v_stop_1839_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_del_object(v___x_1841_);
lean_dec(v_stop_1839_);
lean_dec(v_start_1838_);
lean_dec_ref(v_array_1837_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_b_1836_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_array_fget_borrowed(v_array_1837_, v_start_1838_);
lean_inc(v___x_1845_);
v___x_1846_ = l_Lean_Syntax_reprint(v___x_1845_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1847_; 
lean_del_object(v___x_1841_);
lean_dec(v_stop_1839_);
lean_dec(v_start_1838_);
lean_dec_ref(v_array_1837_);
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
else
{
lean_object* v_val_1848_; uint8_t v___x_1849_; 
v_val_1848_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_val_1848_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1849_ = lean_string_dec_eq(v_val_1834_, v_val_1848_);
lean_dec(v_val_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_del_object(v___x_1841_);
lean_dec(v_stop_1839_);
lean_dec(v_start_1838_);
lean_dec_ref(v_array_1837_);
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_start_1838_, v___x_1852_);
lean_dec(v_start_1838_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1853_);
v___x_1855_ = v___x_1841_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_array_1837_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_stop_1839_);
v___x_1855_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
v_a_1835_ = v___x_1855_;
v_b_1836_ = v___x_1851_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1859_, lean_object* v_stx_1860_, lean_object* v_b_1861_){
_start:
{
lean_object* v_b_1863_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___x_1877_; lean_object* v_a_1879_; 
v___x_1877_ = lean_box(0);
switch(lean_obj_tag(v_stx_1860_))
{
case 2:
{
lean_object* v_info_1888_; lean_object* v_val_1889_; lean_object* v___x_1890_; lean_object* v_s_1891_; 
v_info_1888_ = lean_ctor_get(v_stx_1860_, 0);
v_val_1889_ = lean_ctor_get(v_stx_1860_, 1);
lean_inc(v_info_1888_);
v___x_1890_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1888_, v_val_1889_);
v_s_1891_ = lean_string_append(v_b_1861_, v___x_1890_);
lean_dec_ref(v___x_1890_);
v_a_1879_ = v_s_1891_;
goto v___jp_1878_;
}
case 3:
{
lean_object* v_rawVal_1892_; lean_object* v_info_1893_; lean_object* v_str_1894_; lean_object* v_startPos_1895_; lean_object* v_stopPos_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_s_1899_; 
v_rawVal_1892_ = lean_ctor_get(v_stx_1860_, 1);
v_info_1893_ = lean_ctor_get(v_stx_1860_, 0);
v_str_1894_ = lean_ctor_get(v_rawVal_1892_, 0);
v_startPos_1895_ = lean_ctor_get(v_rawVal_1892_, 1);
v_stopPos_1896_ = lean_ctor_get(v_rawVal_1892_, 2);
v___x_1897_ = lean_string_utf8_extract(v_str_1894_, v_startPos_1895_, v_stopPos_1896_);
lean_inc(v_info_1893_);
v___x_1898_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1893_, v___x_1897_);
lean_dec_ref(v___x_1897_);
v_s_1899_ = lean_string_append(v_b_1861_, v___x_1898_);
lean_dec_ref(v___x_1898_);
v_a_1879_ = v_s_1899_;
goto v___jp_1878_;
}
case 1:
{
lean_object* v_kind_1900_; lean_object* v_args_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_kind_1900_ = lean_ctor_get(v_stx_1860_, 1);
v_args_1901_ = lean_ctor_get(v_stx_1860_, 2);
v___x_1902_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1903_ = lean_name_eq(v_kind_1900_, v___x_1902_);
if (v___x_1903_ == 0)
{
v_a_1879_ = v_b_1861_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_array_get_borrowed(v___x_1877_, v_args_1901_, v___x_1904_);
lean_inc(v___x_1905_);
v___x_1906_ = l_Lean_Syntax_reprint(v___x_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; 
lean_dec_ref_known(v_stx_1860_, 3);
lean_dec_ref(v_b_1861_);
v___x_1907_ = lean_box(0);
return v___x_1907_;
}
else
{
lean_object* v_val_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_val_1908_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_val_1908_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_array_get_size(v_args_1901_);
lean_inc_ref(v_args_1901_);
v___x_1911_ = l_Array_toSubarray___redArg(v_args_1901_, v___x_1909_, v___x_1910_);
v___x_1912_ = lean_box(0);
v___x_1913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1908_, v___x_1911_, v___x_1912_);
lean_dec(v_val_1908_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref_known(v_stx_1860_, 3);
lean_dec_ref(v_b_1861_);
v___x_1914_ = lean_box(0);
return v___x_1914_;
}
else
{
lean_dec_ref_known(v___x_1913_, 1);
v_a_1879_ = v_b_1861_;
goto v___jp_1878_;
}
}
}
}
default: 
{
v_a_1879_ = v_b_1861_;
goto v___jp_1878_;
}
}
v___jp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_b_1863_);
v___x_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
v___jp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; size_t v_sz_1871_; size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v___y_1868_);
v_sz_1871_ = lean_array_size(v___y_1867_);
v___x_1872_ = ((size_t)0ULL);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1859_, v___y_1867_, v_sz_1871_, v___x_1872_, v___x_1870_);
lean_dec_ref(v___y_1867_);
if (lean_obj_tag(v___x_1873_) == 0)
{
return v___x_1869_;
}
else
{
lean_object* v_val_1874_; lean_object* v_fst_1875_; 
v_val_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v_fst_1875_ = lean_ctor_get(v_val_1874_, 0);
if (lean_obj_tag(v_fst_1875_) == 0)
{
lean_object* v_snd_1876_; 
v_snd_1876_ = lean_ctor_get(v_val_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_val_1874_);
v_b_1863_ = v_snd_1876_;
goto v___jp_1862_;
}
else
{
lean_inc_ref(v_fst_1875_);
lean_dec(v_val_1874_);
return v_fst_1875_;
}
}
}
v___jp_1878_:
{
if (lean_obj_tag(v_stx_1860_) == 1)
{
if (v_firstChoiceOnly_1859_ == 0)
{
lean_object* v_args_1880_; 
v_args_1880_ = lean_ctor_get(v_stx_1860_, 2);
lean_inc_ref(v_args_1880_);
lean_dec_ref_known(v_stx_1860_, 3);
v___y_1867_ = v_args_1880_;
v___y_1868_ = v_a_1879_;
goto v___jp_1866_;
}
else
{
lean_object* v_kind_1881_; lean_object* v_args_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v_kind_1881_ = lean_ctor_get(v_stx_1860_, 1);
lean_inc(v_kind_1881_);
v_args_1882_ = lean_ctor_get(v_stx_1860_, 2);
lean_inc_ref(v_args_1882_);
lean_dec_ref_known(v_stx_1860_, 3);
v___x_1883_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1884_ = lean_name_eq(v_kind_1881_, v___x_1883_);
lean_dec(v_kind_1881_);
if (v___x_1884_ == 0)
{
v___y_1867_ = v_args_1882_;
v___y_1868_ = v_a_1879_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_get(v___x_1877_, v_args_1882_, v___x_1885_);
lean_dec_ref(v_args_1882_);
v_stx_1860_ = v___x_1886_;
v_b_1861_ = v_a_1879_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1860_);
v_b_1863_ = v_a_1879_;
goto v___jp_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1915_){
_start:
{
lean_object* v_s_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; 
v_s_1916_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1917_ = 1;
v___x_1918_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1917_, v_stx_1915_, v_s_1916_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_box(0);
return v___x_1919_;
}
else
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_val_1920_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1918_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_a_1924_; lean_object* v___x_1926_; 
v_a_1924_ = lean_ctor_get(v_val_1920_, 0);
lean_inc(v_a_1924_);
lean_dec(v_val_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_a_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1929_, lean_object* v_a_1930_, lean_object* v_b_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1929_, v_a_1930_, v_b_1931_);
lean_dec_ref(v_val_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1933_, lean_object* v_as_1934_, lean_object* v_sz_1935_, lean_object* v_i_1936_, lean_object* v_b_1937_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1938_; size_t v_sz_boxed_1939_; size_t v_i_boxed_1940_; lean_object* v_res_1941_; 
v_firstChoiceOnly_boxed_1938_ = lean_unbox(v_firstChoiceOnly_1933_);
v_sz_boxed_1939_ = lean_unbox_usize(v_sz_1935_);
lean_dec(v_sz_1935_);
v_i_boxed_1940_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_res_1941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1938_, v_as_1934_, v_sz_boxed_1939_, v_i_boxed_1940_, v_b_1937_);
lean_dec_ref(v_as_1934_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1942_, lean_object* v_stx_1943_, lean_object* v_b_1944_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1945_; lean_object* v_res_1946_; 
v_firstChoiceOnly_boxed_1945_ = lean_unbox(v_firstChoiceOnly_1942_);
v_res_1946_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1945_, v_stx_1943_, v_b_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1947_, lean_object* v_inst_1948_, lean_object* v_R_1949_, lean_object* v_a_1950_, lean_object* v_b_1951_, lean_object* v_c_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1947_, v_a_1950_, v_b_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1954_, lean_object* v_inst_1955_, lean_object* v_R_1956_, lean_object* v_a_1957_, lean_object* v_b_1958_, lean_object* v_c_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1954_, v_inst_1955_, v_R_1956_, v_a_1957_, v_b_1958_, v_c_1959_);
lean_dec_ref(v_val_1954_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1969_, lean_object* v_stx_1970_){
_start:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = l_Lean_Syntax_isMissing(v_stx_1970_);
if (v___x_1972_ == 0)
{
if (lean_obj_tag(v_stx_1970_) == 1)
{
lean_object* v_kind_1973_; lean_object* v_args_1974_; 
v_kind_1973_ = lean_ctor_get(v_stx_1970_, 1);
v_args_1974_ = lean_ctor_get(v_stx_1970_, 2);
if (v_firstChoiceOnly_1969_ == 0)
{
goto v___jp_1975_;
}
else
{
lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1985_ = lean_name_eq(v_kind_1973_, v___x_1984_);
if (v___x_1985_ == 0)
{
goto v___jp_1975_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get_borrowed(v___x_1986_, v_args_1974_, v___x_1987_);
v_stx_1970_ = v___x_1988_;
goto _start;
}
}
v___jp_1975_:
{
lean_object* v___x_1976_; size_t v_sz_1977_; size_t v___x_1978_; lean_object* v___x_1979_; lean_object* v_fst_1980_; 
v___x_1976_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1977_ = lean_array_size(v_args_1974_);
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1969_, v_args_1974_, v_sz_1977_, v___x_1978_, v___x_1976_);
v_fst_1980_ = lean_ctor_get(v___x_1979_, 0);
if (lean_obj_tag(v_fst_1980_) == 0)
{
lean_object* v_snd_1981_; lean_object* v___x_1982_; 
v_snd_1981_ = lean_ctor_get(v___x_1979_, 1);
lean_inc(v_snd_1981_);
lean_dec_ref(v___x_1979_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_snd_1981_);
return v___x_1982_;
}
else
{
lean_object* v_val_1983_; 
lean_inc_ref(v_fst_1980_);
lean_dec_ref(v___x_1979_);
v_val_1983_ = lean_ctor_get(v_fst_1980_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v_fst_1980_, 1);
return v_val_1983_;
}
}
}
else
{
lean_object* v___x_1990_; 
v___x_1990_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1990_;
}
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = lean_box(v___x_1972_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v___x_1971_);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1995_, lean_object* v_as_1996_, size_t v_sz_1997_, size_t v_i_1998_, lean_object* v_b_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_usize_dec_lt(v_i_1998_, v_sz_1997_);
if (v___x_2000_ == 0)
{
return v_b_1999_;
}
else
{
lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2019_; 
v_snd_2001_ = lean_ctor_get(v_b_1999_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_b_1999_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_b_1999_, 0);
lean_dec(v_unused_2020_);
v___x_2003_ = v_b_1999_;
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v_b_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_array_uget_borrowed(v_as_1996_, v_i_1998_);
v___x_2006_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1995_, v_a_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2007_);
v___x_2009_ = v___x_2003_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_snd_2001_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_dec(v_snd_2001_);
v_a_2011_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2012_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_a_2011_);
lean_ctor_set(v___x_2003_, 0, v___x_2012_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_a_2011_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
size_t v___x_2015_; size_t v___x_2016_; 
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_add(v_i_1998_, v___x_2015_);
v_i_1998_ = v___x_2016_;
v_b_1999_ = v___x_2014_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_2021_, lean_object* v_as_2022_, lean_object* v_sz_2023_, lean_object* v_i_2024_, lean_object* v_b_2025_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2026_; size_t v_sz_boxed_2027_; size_t v_i_boxed_2028_; lean_object* v_res_2029_; 
v_firstChoiceOnly_boxed_2026_ = lean_unbox(v_firstChoiceOnly_2021_);
v_sz_boxed_2027_ = lean_unbox_usize(v_sz_2023_);
lean_dec(v_sz_2023_);
v_i_boxed_2028_ = lean_unbox_usize(v_i_2024_);
lean_dec(v_i_2024_);
v_res_2029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_2026_, v_as_2022_, v_sz_boxed_2027_, v_i_boxed_2028_, v_b_2025_);
lean_dec_ref(v_as_2022_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_2030_, lean_object* v_stx_2031_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2032_; lean_object* v_res_2033_; 
v_firstChoiceOnly_boxed_2032_ = lean_unbox(v_firstChoiceOnly_2030_);
v_res_2033_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_2032_, v_stx_2031_);
lean_dec(v_stx_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_2034_){
_start:
{
uint8_t v___x_2035_; lean_object* v___y_2037_; lean_object* v___x_2041_; lean_object* v_a_2042_; 
v___x_2035_ = 0;
v___x_2041_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_2035_, v_stx_2034_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
v___y_2037_ = v_a_2042_;
goto v___jp_2036_;
v___jp_2036_:
{
lean_object* v_fst_2038_; 
v_fst_2038_ = lean_ctor_get(v___y_2037_, 0);
lean_inc(v_fst_2038_);
lean_dec_ref(v___y_2037_);
if (lean_obj_tag(v_fst_2038_) == 0)
{
return v___x_2035_;
}
else
{
lean_object* v_val_2039_; uint8_t v___x_2040_; 
v_val_2039_ = lean_ctor_get(v_fst_2038_, 0);
lean_inc(v_val_2039_);
lean_dec_ref_known(v_fst_2038_, 1);
v___x_2040_ = lean_unbox(v_val_2039_);
lean_dec(v_val_2039_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_2043_){
_start:
{
uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_res_2044_ = l_Lean_Syntax_hasMissing(v_stx_2043_);
lean_dec(v_stx_2043_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_2046_, lean_object* v_stx_2047_, lean_object* v_b_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_2046_, v_stx_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_2050_, lean_object* v_stx_2051_, lean_object* v_b_2052_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2053_; lean_object* v_res_2054_; 
v_firstChoiceOnly_boxed_2053_ = lean_unbox(v_firstChoiceOnly_2050_);
v_res_2054_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_2053_, v_stx_2051_, v_b_2052_);
lean_dec_ref(v_b_2052_);
lean_dec(v_stx_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_2055_, uint8_t v_canonicalOnly_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_Syntax_getPos_x3f(v_stx_2055_, v_canonicalOnly_2056_);
if (lean_obj_tag(v___x_2057_) == 1)
{
lean_object* v_val_2058_; lean_object* v___x_2059_; 
v_val_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_val_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2055_, v_canonicalOnly_2056_);
if (lean_obj_tag(v___x_2059_) == 1)
{
lean_object* v_val_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
v_val_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_val_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_val_2058_);
lean_ctor_set(v___x_2064_, 1, v_val_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v___x_2069_; 
lean_dec(v___x_2059_);
lean_dec(v_val_2058_);
v___x_2069_ = lean_box(0);
return v___x_2069_;
}
}
else
{
lean_object* v___x_2070_; 
lean_dec(v___x_2057_);
v___x_2070_ = lean_box(0);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_2071_, lean_object* v_canonicalOnly_2072_){
_start:
{
uint8_t v_canonicalOnly_boxed_2073_; lean_object* v_res_2074_; 
v_canonicalOnly_boxed_2073_ = lean_unbox(v_canonicalOnly_2072_);
v_res_2074_ = l_Lean_Syntax_getRange_x3f(v_stx_2071_, v_canonicalOnly_boxed_2073_);
lean_dec(v_stx_2071_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_2075_, uint8_t v_canonicalOnly_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Syntax_getPos_x3f(v_stx_2075_, v_canonicalOnly_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_box(0);
return v___x_2078_;
}
else
{
lean_object* v_val_2079_; lean_object* v___x_2080_; 
v_val_2079_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2080_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_2075_, v_canonicalOnly_2076_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2081_; 
lean_dec(v_val_2079_);
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v_val_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_val_2082_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_val_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_val_2079_);
lean_ctor_set(v___x_2086_, 1, v_val_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_2091_, lean_object* v_canonicalOnly_2092_){
_start:
{
uint8_t v_canonicalOnly_boxed_2093_; lean_object* v_res_2094_; 
v_canonicalOnly_boxed_2093_ = lean_unbox(v_canonicalOnly_2092_);
v_res_2094_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_2091_, v_canonicalOnly_boxed_2093_);
lean_dec(v_stx_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_2095_, uint8_t v_canonical_2096_){
_start:
{
lean_object* v_start_2097_; lean_object* v_stop_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2107_; 
v_start_2097_ = lean_ctor_get(v_range_2095_, 0);
v_stop_2098_ = lean_ctor_get(v_range_2095_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_range_2095_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2100_ = v_range_2095_;
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_stop_2098_);
lean_inc(v_start_2097_);
lean_dec(v_range_2095_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2102_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2102_, 0, v_start_2097_);
lean_ctor_set(v___x_2102_, 1, v_stop_2098_);
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*2, v_canonical_2096_);
v___x_2103_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 2);
lean_ctor_set(v___x_2100_, 1, v___x_2103_);
lean_ctor_set(v___x_2100_, 0, v___x_2102_);
v___x_2105_ = v___x_2100_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2108_, lean_object* v_canonical_2109_){
_start:
{
uint8_t v_canonical_boxed_2110_; lean_object* v_res_2111_; 
v_canonical_boxed_2110_ = lean_unbox(v_canonical_2109_);
v_res_2111_ = l_Lean_Syntax_ofRange(v_range_2108_, v_canonical_boxed_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2116_, 0, v_stx_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
lean_ctor_set(v___x_2116_, 2, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2117_, lean_object* v_stx_2118_){
_start:
{
lean_object* v_parents_2119_; lean_object* v_idxs_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_parents_2119_ = lean_ctor_get(v_t_2117_, 1);
v_idxs_2120_ = lean_ctor_get(v_t_2117_, 2);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_t_2117_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_t_2117_, 0);
lean_dec(v_unused_2128_);
v___x_2122_ = v_t_2117_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_idxs_2120_);
lean_inc(v_parents_2119_);
lean_dec(v_t_2117_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v_stx_2118_);
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_stx_2118_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_parents_2119_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_idxs_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2129_, lean_object* v_idx_2130_){
_start:
{
lean_object* v_cur_2131_; lean_object* v_parents_2132_; lean_object* v_idxs_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2153_; 
v_cur_2131_ = lean_ctor_get(v_t_2129_, 0);
v_parents_2132_ = lean_ctor_get(v_t_2129_, 1);
v_idxs_2133_ = lean_ctor_get(v_t_2129_, 2);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_t_2129_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2135_ = v_t_2129_;
v_isShared_2136_ = v_isSharedCheck_2153_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_idxs_2133_);
lean_inc(v_parents_2132_);
lean_inc(v_cur_2131_);
lean_dec(v_t_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2153_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = l_Lean_Syntax_getNumArgs(v_cur_2131_);
v___x_2138_ = lean_nat_dec_lt(v_idx_2130_, v___x_2137_);
lean_dec(v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_array_push(v_parents_2132_, v_cur_2131_);
v___x_2141_ = lean_array_push(v_idxs_2133_, v_idx_2130_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 2, v___x_2141_);
lean_ctor_set(v___x_2135_, 1, v___x_2140_);
lean_ctor_set(v___x_2135_, 0, v___x_2139_);
v___x_2143_ = v___x_2135_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2139_);
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
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2145_ = l_Lean_Syntax_getArg(v_cur_2131_, v_idx_2130_);
v___x_2146_ = lean_box(0);
v___x_2147_ = l_Lean_Syntax_setArg(v_cur_2131_, v_idx_2130_, v___x_2146_);
v___x_2148_ = lean_array_push(v_parents_2132_, v___x_2147_);
v___x_2149_ = lean_array_push(v_idxs_2133_, v_idx_2130_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 2, v___x_2149_);
lean_ctor_set(v___x_2135_, 1, v___x_2148_);
lean_ctor_set(v___x_2135_, 0, v___x_2145_);
v___x_2151_ = v___x_2135_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2154_){
_start:
{
lean_object* v_cur_2155_; lean_object* v_parents_2156_; lean_object* v_idxs_2157_; lean_object* v___y_2159_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v_cur_2155_ = lean_ctor_get(v_t_2154_, 0);
v_parents_2156_ = lean_ctor_get(v_t_2154_, 1);
v_idxs_2157_ = lean_ctor_get(v_t_2154_, 2);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_array_get_size(v_parents_2156_);
v___x_2165_ = lean_nat_dec_lt(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
return v_t_2154_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
lean_inc_ref(v_idxs_2157_);
lean_inc_ref(v_parents_2156_);
lean_inc(v_cur_2155_);
lean_dec_ref(v_t_2154_);
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_array_get_size(v_idxs_2157_);
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_sub(v___x_2167_, v___x_2168_);
v___x_2170_ = lean_array_get_borrowed(v___x_2163_, v_idxs_2157_, v___x_2169_);
lean_dec(v___x_2169_);
v___x_2171_ = lean_nat_sub(v___x_2164_, v___x_2168_);
v___x_2172_ = lean_array_get_borrowed(v___x_2166_, v_parents_2156_, v___x_2171_);
lean_dec(v___x_2171_);
v___x_2173_ = l_Lean_Syntax_getNumArgs(v___x_2172_);
v___x_2174_ = lean_nat_dec_lt(v___x_2170_, v___x_2173_);
lean_dec(v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec(v_cur_2155_);
lean_inc(v___x_2172_);
v___y_2159_ = v___x_2172_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2175_; 
lean_inc(v___x_2172_);
v___x_2175_ = l_Lean_Syntax_setArg(v___x_2172_, v___x_2170_, v_cur_2155_);
v___y_2159_ = v___x_2175_;
goto v___jp_2158_;
}
}
v___jp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_array_pop(v_parents_2156_);
v___x_2161_ = lean_array_pop(v_idxs_2157_);
v___x_2162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2159_);
lean_ctor_set(v___x_2162_, 1, v___x_2160_);
lean_ctor_set(v___x_2162_, 2, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2176_){
_start:
{
lean_object* v_parents_2177_; lean_object* v_idxs_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_parents_2177_ = lean_ctor_get(v_t_2176_, 1);
v_idxs_2178_ = lean_ctor_get(v_t_2176_, 2);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_array_get_size(v_parents_2177_);
v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
return v_t_2176_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_inc_ref(v_idxs_2178_);
v___x_2182_ = l_Lean_Syntax_Traverser_up(v_t_2176_);
v___x_2183_ = lean_array_get_size(v_idxs_2178_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_sub(v___x_2183_, v___x_2184_);
v___x_2186_ = lean_array_get(v___x_2179_, v_idxs_2178_, v___x_2185_);
lean_dec(v___x_2185_);
lean_dec_ref(v_idxs_2178_);
v___x_2187_ = lean_nat_sub(v___x_2186_, v___x_2184_);
lean_dec(v___x_2186_);
v___x_2188_ = l_Lean_Syntax_Traverser_down(v___x_2182_, v___x_2187_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2189_){
_start:
{
lean_object* v_parents_2190_; lean_object* v_idxs_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v_parents_2190_ = lean_ctor_get(v_t_2189_, 1);
v_idxs_2191_ = lean_ctor_get(v_t_2189_, 2);
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_array_get_size(v_parents_2190_);
v___x_2194_ = lean_nat_dec_lt(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
return v_t_2189_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_inc_ref(v_idxs_2191_);
v___x_2195_ = l_Lean_Syntax_Traverser_up(v_t_2189_);
v___x_2196_ = lean_array_get_size(v_idxs_2191_);
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = lean_nat_sub(v___x_2196_, v___x_2197_);
v___x_2199_ = lean_array_get(v___x_2192_, v_idxs_2191_, v___x_2198_);
lean_dec(v___x_2198_);
lean_dec_ref(v_idxs_2191_);
v___x_2200_ = lean_nat_add(v___x_2199_, v___x_2197_);
lean_dec(v___x_2199_);
v___x_2201_ = l_Lean_Syntax_Traverser_down(v___x_2195_, v___x_2200_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2202_){
_start:
{
lean_object* v_cur_2203_; 
v_cur_2203_ = lean_ctor_get(v_self_2202_, 0);
lean_inc(v_cur_2203_);
return v_cur_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2204_);
lean_dec_ref(v_self_2204_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2207_, lean_object* v_t_2208_){
_start:
{
lean_object* v_toApplicative_2209_; lean_object* v_toFunctor_2210_; lean_object* v_map_2211_; lean_object* v_get_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; 
v_toApplicative_2209_ = lean_ctor_get(v_inst_2207_, 0);
lean_inc_ref(v_toApplicative_2209_);
lean_dec_ref(v_inst_2207_);
v_toFunctor_2210_ = lean_ctor_get(v_toApplicative_2209_, 0);
lean_inc_ref(v_toFunctor_2210_);
lean_dec_ref(v_toApplicative_2209_);
v_map_2211_ = lean_ctor_get(v_toFunctor_2210_, 0);
lean_inc(v_map_2211_);
lean_dec_ref(v_toFunctor_2210_);
v_get_2212_ = lean_ctor_get(v_t_2208_, 0);
lean_inc(v_get_2212_);
lean_dec_ref(v_t_2208_);
v___f_2213_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2214_ = lean_apply_4(v_map_2211_, lean_box(0), lean_box(0), v___f_2213_, v_get_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2215_, lean_object* v_inst_2216_, lean_object* v_t_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2216_, v_t_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2219_, lean_object* v_s_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = l_Lean_Syntax_Traverser_setCur(v_s_2220_, v_stx_2219_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2224_, lean_object* v_stx_2225_){
_start:
{
lean_object* v_modifyGet_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; 
v_modifyGet_2226_ = lean_ctor_get(v_t_2224_, 2);
lean_inc(v_modifyGet_2226_);
lean_dec_ref(v_t_2224_);
v___f_2227_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2227_, 0, v_stx_2225_);
v___x_2228_ = lean_apply_2(v_modifyGet_2226_, lean_box(0), v___f_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2229_, lean_object* v_t_2230_, lean_object* v_stx_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2230_, v_stx_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2233_, lean_object* v_s_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = l_Lean_Syntax_Traverser_down(v_s_2234_, v_idx_2233_);
v___x_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2238_, lean_object* v_idx_2239_){
_start:
{
lean_object* v_modifyGet_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; 
v_modifyGet_2240_ = lean_ctor_get(v_t_2238_, 2);
lean_inc(v_modifyGet_2240_);
lean_dec_ref(v_t_2238_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2241_, 0, v_idx_2239_);
v___x_2242_ = lean_apply_2(v_modifyGet_2240_, lean_box(0), v___f_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2243_, lean_object* v_t_2244_, lean_object* v_idx_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2244_, v_idx_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = l_Lean_Syntax_Traverser_up(v_s_2247_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2252_){
_start:
{
lean_object* v_modifyGet_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; 
v_modifyGet_2253_ = lean_ctor_get(v_t_2252_, 2);
lean_inc(v_modifyGet_2253_);
lean_dec_ref(v_t_2252_);
v___f_2254_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2255_ = lean_apply_2(v_modifyGet_2253_, lean_box(0), v___f_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2256_, lean_object* v_t_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_box(0);
v___x_2261_ = l_Lean_Syntax_Traverser_left(v_s_2259_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2264_){
_start:
{
lean_object* v_modifyGet_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v_modifyGet_2265_ = lean_ctor_get(v_t_2264_, 2);
lean_inc(v_modifyGet_2265_);
lean_dec_ref(v_t_2264_);
v___f_2266_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2267_ = lean_apply_2(v_modifyGet_2265_, lean_box(0), v___f_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2268_, lean_object* v_t_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = l_Lean_Syntax_Traverser_right(v_s_2271_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2276_){
_start:
{
lean_object* v_modifyGet_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; 
v_modifyGet_2277_ = lean_ctor_get(v_t_2276_, 2);
lean_inc(v_modifyGet_2277_);
lean_dec_ref(v_t_2276_);
v___f_2278_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2279_ = lean_apply_2(v_modifyGet_2277_, lean_box(0), v___f_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2280_, lean_object* v_t_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2283_, lean_object* v_st_2284_){
_start:
{
lean_object* v_idxs_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_idxs_2285_ = lean_ctor_get(v_st_2284_, 2);
v___x_2286_ = lean_array_get_size(v_idxs_2285_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_sub(v___x_2286_, v___x_2287_);
v___x_2289_ = lean_nat_dec_lt(v___x_2288_, v___x_2286_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec(v___x_2288_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_apply_2(v_toPure_2283_, lean_box(0), v___x_2290_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_array_fget_borrowed(v_idxs_2285_, v___x_2288_);
lean_dec(v___x_2288_);
lean_inc(v___x_2292_);
v___x_2293_ = lean_apply_2(v_toPure_2283_, lean_box(0), v___x_2292_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2294_, lean_object* v_st_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2294_, v_st_2295_);
lean_dec_ref(v_st_2295_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2297_, lean_object* v_t_2298_){
_start:
{
lean_object* v_toApplicative_2299_; lean_object* v_toBind_2300_; lean_object* v_get_2301_; lean_object* v_toPure_2302_; lean_object* v___f_2303_; lean_object* v___x_2304_; 
v_toApplicative_2299_ = lean_ctor_get(v_inst_2297_, 0);
lean_inc_ref(v_toApplicative_2299_);
v_toBind_2300_ = lean_ctor_get(v_inst_2297_, 1);
lean_inc(v_toBind_2300_);
lean_dec_ref(v_inst_2297_);
v_get_2301_ = lean_ctor_get(v_t_2298_, 0);
lean_inc(v_get_2301_);
lean_dec_ref(v_t_2298_);
v_toPure_2302_ = lean_ctor_get(v_toApplicative_2299_, 1);
lean_inc(v_toPure_2302_);
lean_dec_ref(v_toApplicative_2299_);
v___f_2303_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2303_, 0, v_toPure_2302_);
v___x_2304_ = lean_apply_4(v_toBind_2300_, lean_box(0), lean_box(0), v_get_2301_, v___f_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2305_, lean_object* v_inst_2306_, lean_object* v_t_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2306_, v_t_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2309_, lean_object* v_i_2310_){
_start:
{
lean_object* v_args_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_args_2311_ = lean_ctor_get(v_n_2309_, 2);
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_array_get_borrowed(v___x_2312_, v_args_2311_, v_i_2310_);
v___x_2314_ = l_Lean_Syntax_getId(v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2315_, lean_object* v_i_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_SyntaxNode_getIdAt(v_n_2315_, v_i_2316_);
lean_dec(v_i_2316_);
lean_dec(v_n_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2320_ = lean_box(2);
v___x_2321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v___x_2319_);
lean_ctor_set(v___x_2321_, 2, v_args_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2327_){
_start:
{
if (lean_obj_tag(v_x_2327_) == 1)
{
lean_object* v_kind_2328_; 
v_kind_2328_ = lean_ctor_get(v_x_2327_, 1);
if (lean_obj_tag(v_kind_2328_) == 1)
{
lean_object* v_pre_2329_; lean_object* v_str_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_pre_2329_ = lean_ctor_get(v_kind_2328_, 0);
v_str_2330_ = lean_ctor_get(v_kind_2328_, 1);
v___x_2331_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2332_ = lean_string_dec_eq(v_str_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2334_ = lean_string_dec_eq(v_str_2330_, v___x_2333_);
if (v___x_2334_ == 0)
{
return v___x_2334_;
}
else
{
if (lean_obj_tag(v_pre_2329_) == 1)
{
lean_object* v_pre_2335_; 
v_pre_2335_ = lean_ctor_get(v_pre_2329_, 0);
if (lean_obj_tag(v_pre_2335_) == 1)
{
lean_object* v_pre_2336_; 
v_pre_2336_ = lean_ctor_get(v_pre_2335_, 0);
if (lean_obj_tag(v_pre_2336_) == 1)
{
lean_object* v_pre_2337_; 
v_pre_2337_ = lean_ctor_get(v_pre_2336_, 0);
if (lean_obj_tag(v_pre_2337_) == 0)
{
lean_object* v_str_2338_; lean_object* v_str_2339_; lean_object* v_str_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_str_2338_ = lean_ctor_get(v_pre_2329_, 1);
v_str_2339_ = lean_ctor_get(v_pre_2335_, 1);
v_str_2340_ = lean_ctor_get(v_pre_2336_, 1);
v___x_2341_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2342_ = lean_string_dec_eq(v_str_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
return v___x_2332_;
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2344_ = lean_string_dec_eq(v_str_2339_, v___x_2343_);
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2346_ = lean_string_dec_eq(v_str_2338_, v___x_2345_);
return v___x_2346_;
}
}
}
else
{
return v___x_2332_;
}
}
else
{
return v___x_2332_;
}
}
else
{
return v___x_2332_;
}
}
else
{
return v___x_2332_;
}
}
}
else
{
return v___x_2332_;
}
}
else
{
uint8_t v___x_2347_; 
v___x_2347_ = 0;
return v___x_2347_;
}
}
else
{
uint8_t v___x_2348_; 
v___x_2348_ = 0;
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = l_Lean_Syntax_isQuot(v_x_2349_);
lean_dec(v_x_2349_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___y_2361_; uint8_t v___x_2367_; 
v___x_2358_ = l_Lean_Syntax_getNumArgs(v_stx_2357_);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_dec_eq(v___x_2358_, v___x_2359_);
lean_dec(v___x_2358_);
if (v___x_2367_ == 0)
{
v___y_2361_ = v_stx_2357_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = l_Lean_Syntax_getArg(v_stx_2357_, v___x_2368_);
lean_dec(v_stx_2357_);
v___y_2361_ = v___x_2369_;
goto v___jp_2360_;
}
v___jp_2360_:
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2361_);
v___x_2363_ = l_Lean_Syntax_isOfKind(v___y_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_Syntax_getArg(v___y_2361_, v___x_2359_);
lean_dec(v___y_2361_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_unsigned_to_nat(3u);
v___x_2366_ = l_Lean_Syntax_getArg(v___y_2361_, v___x_2365_);
lean_dec(v___y_2361_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2371_){
_start:
{
if (lean_obj_tag(v_x_2371_) == 1)
{
lean_object* v_kind_2372_; 
v_kind_2372_ = lean_ctor_get(v_x_2371_, 1);
if (lean_obj_tag(v_kind_2372_) == 1)
{
lean_object* v_str_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_str_2373_ = lean_ctor_get(v_kind_2372_, 1);
v___x_2374_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2375_ = lean_string_dec_eq(v_str_2373_, v___x_2374_);
return v___x_2375_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = 0;
return v___x_2376_;
}
}
else
{
uint8_t v___x_2377_; 
v___x_2377_ = 0;
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Lean_Syntax_isAntiquot(v_x_2378_);
lean_dec(v_x_2378_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object* v___x_2381_, uint8_t v___x_2382_, lean_object* v_as_2383_, size_t v_i_2384_, size_t v_stop_2385_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = lean_usize_dec_eq(v_i_2384_, v_stop_2385_);
if (v___x_2386_ == 0)
{
uint8_t v___x_2387_; uint8_t v___y_2389_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2387_ = 1;
v___x_2393_ = lean_array_uget_borrowed(v_as_2383_, v_i_2384_);
v___x_2394_ = l_Lean_Syntax_isAntiquot(v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2396_ = lean_nat_dec_lt(v___x_2395_, v___x_2381_);
v___y_2389_ = v___x_2396_;
goto v___jp_2388_;
}
else
{
v___y_2389_ = v___x_2382_;
goto v___jp_2388_;
}
v___jp_2388_:
{
if (v___y_2389_ == 0)
{
size_t v___x_2390_; size_t v___x_2391_; 
v___x_2390_ = ((size_t)1ULL);
v___x_2391_ = lean_usize_add(v_i_2384_, v___x_2390_);
v_i_2384_ = v___x_2391_;
goto _start;
}
else
{
return v___x_2387_;
}
}
}
else
{
uint8_t v___x_2397_; 
v___x_2397_ = 0;
return v___x_2397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v_as_2400_, lean_object* v_i_2401_, lean_object* v_stop_2402_){
_start:
{
uint8_t v___x_341__boxed_2403_; size_t v_i_boxed_2404_; size_t v_stop_boxed_2405_; uint8_t v_res_2406_; lean_object* v_r_2407_; 
v___x_341__boxed_2403_ = lean_unbox(v___x_2399_);
v_i_boxed_2404_ = lean_unbox_usize(v_i_2401_);
lean_dec(v_i_2401_);
v_stop_boxed_2405_ = lean_unbox_usize(v_stop_2402_);
lean_dec(v_stop_2402_);
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2398_, v___x_341__boxed_2403_, v_as_2400_, v_i_boxed_2404_, v_stop_boxed_2405_);
lean_dec_ref(v_as_2400_);
lean_dec(v___x_2398_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2408_){
_start:
{
uint8_t v___x_2409_; 
v___x_2409_ = l_Lean_Syntax_isAntiquot(v_stx_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2408_);
v___x_2411_ = l_Lean_Syntax_isOfKind(v_stx_2408_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_dec(v_stx_2408_);
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = l_Lean_Syntax_getNumArgs(v_stx_2408_);
v___x_2414_ = lean_nat_dec_lt(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_dec(v___x_2413_);
lean_dec(v_stx_2408_);
return v___x_2414_;
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2415_ = l_Lean_Syntax_getArgs(v_stx_2408_);
lean_dec(v_stx_2408_);
v___x_2416_ = lean_array_get_size(v___x_2415_);
v___x_2417_ = lean_nat_dec_lt(v___x_2412_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_dec_ref(v___x_2415_);
lean_dec(v___x_2413_);
return v___x_2414_;
}
else
{
if (v___x_2417_ == 0)
{
lean_dec_ref(v___x_2415_);
lean_dec(v___x_2413_);
return v___x_2414_;
}
else
{
size_t v___x_2418_; size_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___x_2416_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2413_, v___x_2409_, v___x_2415_, v___x_2418_, v___x_2419_);
lean_dec_ref(v___x_2415_);
lean_dec(v___x_2413_);
if (v___x_2420_ == 0)
{
return v___x_2417_;
}
else
{
return v___x_2409_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_2408_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_Lean_Syntax_isAntiquots(v_stx_2421_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2424_){
_start:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2424_);
v___x_2426_ = l_Lean_Syntax_isOfKind(v_stx_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
return v_stx_2424_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = l_Lean_Syntax_getArg(v_stx_2424_, v___x_2427_);
lean_dec(v_stx_2424_);
return v___x_2428_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2431_ = l_Lean_mkAtom(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2434_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2435_ = lean_unsigned_to_nat(4u);
v___x_2436_ = lean_mk_empty_array_with_capacity(v___x_2435_);
v___x_2437_ = lean_array_push(v___x_2436_, v___x_2434_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2446_ = l_Lean_mkAtom(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2447_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2448_ = lean_unsigned_to_nat(2u);
v___x_2449_ = lean_mk_empty_array_with_capacity(v___x_2448_);
v___x_2450_ = lean_array_push(v___x_2449_, v___x_2447_);
return v___x_2450_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2462_ = l_Lean_mkAtom(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2465_ = l_Lean_mkAtom(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2466_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2467_ = lean_unsigned_to_nat(3u);
v___x_2468_ = lean_mk_empty_array_with_capacity(v___x_2467_);
v___x_2469_ = lean_array_push(v___x_2468_, v___x_2466_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2470_, lean_object* v_term_2471_, lean_object* v_nesting_2472_, lean_object* v_name_2473_, uint8_t v_isPseudoKind_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_nesting_2479_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2498_; uint8_t v___x_2506_; 
v___x_2475_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2476_ = lean_mk_array(v_nesting_2472_, v___x_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2478_ = lean_box(2);
v_nesting_2479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2479_, 0, v___x_2478_);
lean_ctor_set(v_nesting_2479_, 1, v___x_2477_);
lean_ctor_set(v_nesting_2479_, 2, v___x_2476_);
v___x_2506_ = l_Lean_Syntax_isIdent(v_term_2471_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2471_);
v___x_2508_ = l_Lean_Syntax_isOfKind(v_term_2471_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2509_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2510_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2511_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2512_ = lean_array_push(v___x_2511_, v_term_2471_);
v___x_2513_ = lean_array_push(v___x_2512_, v___x_2510_);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2478_);
lean_ctor_set(v___x_2514_, 1, v___x_2509_);
lean_ctor_set(v___x_2514_, 2, v___x_2513_);
v___y_2498_ = v___x_2514_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = l_Lean_Syntax_getArg(v_term_2471_, v___x_2515_);
lean_dec(v_term_2471_);
v___y_2498_ = v___x_2516_;
goto v___jp_2497_;
}
}
else
{
v___y_2498_ = v_term_2471_;
goto v___jp_2497_;
}
v___jp_2480_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_inc(v___y_2483_);
v___x_2484_ = l_Lean_Name_append(v_kind_2470_, v___y_2483_);
v___x_2485_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2486_ = l_Lean_Name_append(v___x_2484_, v___x_2485_);
v___x_2487_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2488_ = lean_array_push(v___x_2487_, v_nesting_2479_);
v___x_2489_ = lean_array_push(v___x_2488_, v___y_2481_);
v___x_2490_ = lean_array_push(v___x_2489_, v___y_2482_);
v___x_2491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2478_);
lean_ctor_set(v___x_2491_, 1, v___x_2486_);
lean_ctor_set(v___x_2491_, 2, v___x_2490_);
return v___x_2491_;
}
v___jp_2492_:
{
if (v_isPseudoKind_2474_ == 0)
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_box(0);
v___y_2481_ = v___y_2493_;
v___y_2482_ = v___y_2494_;
v___y_2483_ = v___x_2495_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2496_; 
v___x_2496_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2481_ = v___y_2493_;
v___y_2482_ = v___y_2494_;
v___y_2483_ = v___x_2496_;
goto v___jp_2480_;
}
}
v___jp_2497_:
{
if (lean_obj_tag(v_name_2473_) == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2493_ = v___y_2498_;
v___y_2494_ = v___x_2499_;
goto v___jp_2492_;
}
else
{
lean_object* v_val_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_val_2500_ = lean_ctor_get(v_name_2473_, 0);
lean_inc(v_val_2500_);
lean_dec_ref_known(v_name_2473_, 1);
v___x_2501_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2502_ = l_Lean_mkAtom(v_val_2500_);
v___x_2503_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2504_ = lean_array_push(v___x_2503_, v___x_2502_);
v___x_2505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2478_);
lean_ctor_set(v___x_2505_, 1, v___x_2501_);
lean_ctor_set(v___x_2505_, 2, v___x_2504_);
v___y_2493_ = v___y_2498_;
v___y_2494_ = v___x_2505_;
goto v___jp_2492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2517_, lean_object* v_term_2518_, lean_object* v_nesting_2519_, lean_object* v_name_2520_, lean_object* v_isPseudoKind_2521_){
_start:
{
uint8_t v_isPseudoKind_boxed_2522_; lean_object* v_res_2523_; 
v_isPseudoKind_boxed_2522_ = lean_unbox(v_isPseudoKind_2521_);
v_res_2523_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2517_, v_term_2518_, v_nesting_2519_, v_name_2520_, v_isPseudoKind_boxed_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2524_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2525_ = lean_unsigned_to_nat(1u);
v___x_2526_ = l_Lean_Syntax_getArg(v_stx_2524_, v___x_2525_);
v___x_2527_ = l_Lean_Syntax_getArgs(v___x_2526_);
lean_dec(v___x_2526_);
v___x_2528_ = lean_array_get_size(v___x_2527_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_nat_dec_eq(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
uint8_t v___x_2531_; 
v___x_2531_ = 1;
return v___x_2531_;
}
else
{
uint8_t v___x_2532_; 
v___x_2532_ = 0;
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2533_){
_start:
{
uint8_t v_res_2534_; lean_object* v_r_2535_; 
v_res_2534_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2533_);
lean_dec(v_stx_2533_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2536_){
_start:
{
uint8_t v___x_2537_; 
v___x_2537_ = l_Lean_Syntax_isAntiquot(v_stx_2536_);
if (v___x_2537_ == 0)
{
return v_stx_2536_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = l_Lean_Syntax_getArg(v_stx_2536_, v___x_2538_);
v___x_2540_ = l_Lean_Syntax_getArgs(v___x_2539_);
lean_dec(v___x_2539_);
v___x_2541_ = lean_array_pop(v___x_2540_);
v___x_2542_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2543_ = lean_box(2);
v___x_2544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2542_);
lean_ctor_set(v___x_2544_, 2, v___x_2541_);
v___x_2545_ = l_Lean_Syntax_setArg(v_stx_2536_, v___x_2538_, v___x_2544_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2546_){
_start:
{
lean_object* v___y_2548_; uint8_t v___x_2559_; 
v___x_2559_ = l_Lean_Syntax_isAntiquot(v_stx_2546_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_unsigned_to_nat(3u);
v___x_2561_ = l_Lean_Syntax_getArg(v_stx_2546_, v___x_2560_);
v___y_2548_ = v___x_2561_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_unsigned_to_nat(2u);
v___x_2563_ = l_Lean_Syntax_getArg(v_stx_2546_, v___x_2562_);
v___y_2548_ = v___x_2563_;
goto v___jp_2547_;
}
v___jp_2547_:
{
uint8_t v___x_2549_; 
v___x_2549_ = l_Lean_Syntax_isIdent(v___y_2548_);
if (v___x_2549_ == 0)
{
uint8_t v___x_2550_; 
v___x_2550_ = l_Lean_Syntax_isAtom(v___y_2548_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_unsigned_to_nat(1u);
v___x_2552_ = l_Lean_Syntax_getArg(v___y_2548_, v___x_2551_);
lean_dec(v___y_2548_);
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2553_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_mk_empty_array_with_capacity(v___x_2554_);
v___x_2556_ = lean_array_push(v___x_2555_, v___y_2548_);
v___x_2557_ = lean_box(2);
v___x_2558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
lean_ctor_set(v___x_2558_, 1, v___x_2553_);
lean_ctor_set(v___x_2558_, 2, v___x_2556_);
return v___x_2558_;
}
}
else
{
return v___y_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2564_);
lean_dec(v_stx_2564_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2566_){
_start:
{
if (lean_obj_tag(v_x_2566_) == 1)
{
lean_object* v_kind_2567_; 
v_kind_2567_ = lean_ctor_get(v_x_2566_, 1);
if (lean_obj_tag(v_kind_2567_) == 1)
{
lean_object* v_pre_2568_; lean_object* v_str_2569_; 
v_pre_2568_ = lean_ctor_get(v_kind_2567_, 0);
v_str_2569_ = lean_ctor_get(v_kind_2567_, 1);
if (lean_obj_tag(v_pre_2568_) == 1)
{
lean_object* v_pre_2575_; lean_object* v_str_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_pre_2575_ = lean_ctor_get(v_pre_2568_, 0);
v_str_2576_ = lean_ctor_get(v_pre_2568_, 1);
v___x_2577_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2578_ = lean_string_dec_eq(v_str_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2579_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2580_ = lean_string_dec_eq(v_str_2569_, v___x_2579_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_box(0);
return v___x_2581_;
}
else
{
goto v___jp_2570_;
}
}
else
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2583_ = lean_string_dec_eq(v_str_2569_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_box(0);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_box(v___x_2583_);
lean_inc(v_pre_2575_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_pre_2575_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
}
else
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2589_ = lean_string_dec_eq(v_str_2569_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
v___x_2590_ = lean_box(0);
return v___x_2590_;
}
else
{
goto v___jp_2570_;
}
}
v___jp_2570_:
{
uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2571_ = 0;
v___x_2572_ = lean_box(v___x_2571_);
lean_inc(v_pre_2568_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_pre_2568_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_box(0);
return v___x_2591_;
}
}
else
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_box(0);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2593_);
lean_dec(v_x_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2595_, size_t v_i_2596_, size_t v_stop_2597_, lean_object* v_b_2598_){
_start:
{
lean_object* v___y_2600_; uint8_t v___x_2604_; 
v___x_2604_ = lean_usize_dec_eq(v_i_2596_, v_stop_2597_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_array_uget_borrowed(v_as_2595_, v_i_2596_);
v___x_2606_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
v___y_2600_ = v_b_2598_;
goto v___jp_2599_;
}
else
{
lean_object* v_val_2607_; lean_object* v___x_2608_; 
v_val_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_array_push(v_b_2598_, v_val_2607_);
v___y_2600_ = v___x_2608_;
goto v___jp_2599_;
}
}
else
{
return v_b_2598_;
}
v___jp_2599_:
{
size_t v___x_2601_; size_t v___x_2602_; 
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2596_, v___x_2601_);
v_i_2596_ = v___x_2602_;
v_b_2598_ = v___y_2600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2609_, lean_object* v_i_2610_, lean_object* v_stop_2611_, lean_object* v_b_2612_){
_start:
{
size_t v_i_boxed_2613_; size_t v_stop_boxed_2614_; lean_object* v_res_2615_; 
v_i_boxed_2613_ = lean_unbox_usize(v_i_2610_);
lean_dec(v_i_2610_);
v_stop_boxed_2614_ = lean_unbox_usize(v_stop_2611_);
lean_dec(v_stop_2611_);
v_res_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2609_, v_i_boxed_2613_, v_stop_boxed_2614_, v_b_2612_);
lean_dec_ref(v_as_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2618_, lean_object* v_start_2619_, lean_object* v_stop_2620_){
_start:
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2622_ = lean_nat_dec_lt(v_start_2619_, v_stop_2620_);
if (v___x_2622_ == 0)
{
return v___x_2621_;
}
else
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_array_get_size(v_as_2618_);
v___x_2624_ = lean_nat_dec_le(v_stop_2620_, v___x_2623_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_nat_dec_lt(v_start_2619_, v___x_2623_);
if (v___x_2625_ == 0)
{
return v___x_2621_;
}
else
{
size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_usize_of_nat(v_start_2619_);
v___x_2627_ = lean_usize_of_nat(v___x_2623_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2618_, v___x_2626_, v___x_2627_, v___x_2621_);
return v___x_2628_;
}
}
else
{
size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_usize_of_nat(v_start_2619_);
v___x_2630_ = lean_usize_of_nat(v_stop_2620_);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2618_, v___x_2629_, v___x_2630_, v___x_2621_);
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2632_, lean_object* v_start_2633_, lean_object* v_stop_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2632_, v_start_2633_, v_stop_2634_);
lean_dec(v_stop_2634_);
lean_dec(v_start_2633_);
lean_dec_ref(v_as_2632_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2636_){
_start:
{
lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2636_);
v___x_2638_ = l_Lean_Syntax_isOfKind(v_stx_2636_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2636_);
lean_dec(v_stx_2636_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_box(0);
return v___x_2640_;
}
else
{
lean_object* v_val_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_val_2641_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_val_2641_);
lean_dec_ref_known(v___x_2639_, 1);
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2643_, 0, v_val_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
return v___x_2643_;
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2644_ = l_Lean_Syntax_getArgs(v_stx_2636_);
lean_dec(v_stx_2636_);
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = lean_array_get_size(v___x_2644_);
v___x_2647_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2644_, v___x_2645_, v___x_2646_);
lean_dec_ref(v___x_2644_);
v___x_2648_ = lean_array_to_list(v___x_2647_);
return v___x_2648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2650_){
_start:
{
if (lean_obj_tag(v_x_2650_) == 1)
{
lean_object* v_kind_2651_; 
v_kind_2651_ = lean_ctor_get(v_x_2650_, 1);
if (lean_obj_tag(v_kind_2651_) == 1)
{
lean_object* v_pre_2652_; lean_object* v_str_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v_pre_2652_ = lean_ctor_get(v_kind_2651_, 0);
v_str_2653_ = lean_ctor_get(v_kind_2651_, 1);
v___x_2654_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2655_ = lean_string_dec_eq(v_str_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_box(0);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; 
lean_inc(v_pre_2652_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_pre_2652_);
return v___x_2657_;
}
}
else
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_box(0);
return v___x_2658_;
}
}
else
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_box(0);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2660_);
lean_dec(v_x_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2662_);
if (lean_obj_tag(v___x_2663_) == 0)
{
uint8_t v___x_2664_; 
v___x_2664_ = 0;
return v___x_2664_;
}
else
{
uint8_t v___x_2665_; 
lean_dec_ref_known(v___x_2663_, 1);
v___x_2665_ = 1;
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2666_);
lean_dec(v_stx_2666_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2669_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_unsigned_to_nat(3u);
v___x_2671_ = l_Lean_Syntax_getArg(v_stx_2669_, v___x_2670_);
v___x_2672_ = l_Lean_Syntax_getArgs(v___x_2671_);
lean_dec(v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2673_);
lean_dec(v_stx_2673_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_unsigned_to_nat(1u);
v___x_2678_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2677_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_unsigned_to_nat(5u);
v___x_2680_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2679_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2681_);
lean_dec(v_stx_2681_);
return v_res_2682_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2688_ = l_Lean_mkAtom(v___x_2687_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2691_ = l_Lean_mkAtom(v___x_2690_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2692_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2693_ = lean_unsigned_to_nat(6u);
v___x_2694_ = lean_mk_empty_array_with_capacity(v___x_2693_);
v___x_2695_ = lean_array_push(v___x_2694_, v___x_2692_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2696_, lean_object* v_contents_2697_, lean_object* v_suffix_2698_, lean_object* v_nesting_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v_nesting_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2700_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2701_ = lean_mk_array(v_nesting_2699_, v___x_2700_);
v___x_2702_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2703_ = lean_box(2);
v_nesting_2704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2704_, 0, v___x_2703_);
lean_ctor_set(v_nesting_2704_, 1, v___x_2702_);
lean_ctor_set(v_nesting_2704_, 2, v___x_2701_);
v___x_2705_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2706_ = l_Lean_Name_append(v_kind_2696_, v___x_2705_);
v___x_2707_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2703_);
lean_ctor_set(v___x_2708_, 1, v___x_2702_);
lean_ctor_set(v___x_2708_, 2, v_contents_2697_);
v___x_2709_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2710_ = l_Lean_mkAtom(v_suffix_2698_);
v___x_2711_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2712_ = lean_array_push(v___x_2711_, v_nesting_2704_);
v___x_2713_ = lean_array_push(v___x_2712_, v___x_2707_);
v___x_2714_ = lean_array_push(v___x_2713_, v___x_2708_);
v___x_2715_ = lean_array_push(v___x_2714_, v___x_2709_);
v___x_2716_ = lean_array_push(v___x_2715_, v___x_2710_);
v___x_2717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2703_);
lean_ctor_set(v___x_2717_, 1, v___x_2706_);
lean_ctor_set(v___x_2717_, 2, v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2719_){
_start:
{
if (lean_obj_tag(v_x_2719_) == 1)
{
lean_object* v_kind_2720_; 
v_kind_2720_ = lean_ctor_get(v_x_2719_, 1);
if (lean_obj_tag(v_kind_2720_) == 1)
{
lean_object* v_pre_2721_; lean_object* v_str_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v_pre_2721_ = lean_ctor_get(v_kind_2720_, 0);
v_str_2722_ = lean_ctor_get(v_kind_2720_, 1);
v___x_2723_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2724_ = lean_string_dec_eq(v_str_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_box(0);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; 
lean_inc(v_pre_2721_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_pre_2721_);
return v___x_2726_;
}
}
else
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_box(0);
return v___x_2727_;
}
}
else
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_box(0);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2729_);
lean_dec(v_x_2729_);
return v_res_2730_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2731_);
if (lean_obj_tag(v___x_2732_) == 0)
{
uint8_t v___x_2733_; 
v___x_2733_ = 0;
return v___x_2733_;
}
else
{
uint8_t v___x_2734_; 
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = 1;
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2735_){
_start:
{
uint8_t v_res_2736_; lean_object* v_r_2737_; 
v_res_2736_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2735_);
lean_dec(v_stx_2735_);
v_r_2737_ = lean_box(v_res_2736_);
return v_r_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2738_){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = l_Lean_Syntax_getArg(v_stx_2738_, v___x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2741_);
lean_dec(v_stx_2741_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2745_, lean_object* v_inner_2746_, lean_object* v_suffix_2747_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2748_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2749_ = l_Lean_Name_append(v_kind_2745_, v___x_2748_);
v___x_2750_ = l_Lean_mkAtom(v_suffix_2747_);
v___x_2751_ = lean_unsigned_to_nat(2u);
v___x_2752_ = lean_mk_empty_array_with_capacity(v___x_2751_);
v___x_2753_ = lean_array_push(v___x_2752_, v_inner_2746_);
v___x_2754_ = lean_array_push(v___x_2753_, v___x_2750_);
v___x_2755_ = lean_box(2);
v___x_2756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2749_);
lean_ctor_set(v___x_2756_, 2, v___x_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2760_){
_start:
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2762_ = l_Lean_Syntax_isOfKind(v_stx_2760_, v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2763_){
_start:
{
uint8_t v_res_2764_; lean_object* v_r_2765_; 
v_res_2764_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2763_);
v_r_2765_ = lean_box(v_res_2764_);
return v_r_2765_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2766_){
_start:
{
uint8_t v___x_2767_; 
v___x_2767_ = l_Lean_Syntax_isAntiquot(v_stx_2766_);
if (v___x_2767_ == 0)
{
uint8_t v___x_2768_; 
v___x_2768_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2766_);
if (v___x_2768_ == 0)
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2766_);
if (v___x_2769_ == 0)
{
uint8_t v___x_2770_; 
v___x_2770_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2766_);
return v___x_2770_;
}
else
{
lean_dec(v_stx_2766_);
return v___x_2769_;
}
}
else
{
lean_dec(v_stx_2766_);
return v___x_2768_;
}
}
else
{
lean_dec(v_stx_2766_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2771_){
_start:
{
uint8_t v_res_2772_; lean_object* v_r_2773_; 
v_res_2772_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2771_);
v_r_2773_ = lean_box(v_res_2772_);
return v_r_2773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2777_, lean_object* v_stx_2778_, lean_object* v_visit_2779_, lean_object* v_stack_2780_, lean_object* v_accept_2781_, lean_object* v_a_2782_, lean_object* v_b_2783_){
_start:
{
lean_object* v_a_2785_; uint8_t v___x_2789_; 
v___x_2789_ = lean_nat_dec_lt(v_a_2782_, v_upperBound_2777_);
if (v___x_2789_ == 0)
{
lean_dec(v_a_2782_);
lean_dec_ref(v_accept_2781_);
lean_dec(v_stack_2780_);
lean_dec_ref(v_visit_2779_);
lean_dec(v_stx_2778_);
lean_inc_ref(v_b_2783_);
return v_b_2783_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2790_ = lean_box(0);
v___x_2791_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2792_ = l_Lean_Syntax_getArg(v_stx_2778_, v_a_2782_);
lean_inc_ref(v_visit_2779_);
lean_inc(v___x_2792_);
v___x_2793_ = lean_apply_1(v_visit_2779_, v___x_2792_);
v___x_2794_ = lean_unbox(v___x_2793_);
if (v___x_2794_ == 0)
{
lean_dec(v___x_2792_);
v_a_2785_ = v___x_2791_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_inc(v_a_2782_);
lean_inc(v_stx_2778_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_stx_2778_);
lean_ctor_set(v___x_2795_, 1, v_a_2782_);
lean_inc(v_stack_2780_);
v___x_2796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v_stack_2780_);
lean_inc_ref(v_accept_2781_);
lean_inc_ref(v_visit_2779_);
v___x_2797_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2779_, v_accept_2781_, v___x_2796_, v___x_2792_);
if (lean_obj_tag(v___x_2797_) == 1)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v_a_2782_);
lean_dec_ref(v_accept_2781_);
lean_dec(v_stack_2780_);
lean_dec_ref(v_visit_2779_);
lean_dec(v_stx_2778_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2790_);
return v___x_2799_;
}
else
{
lean_dec(v___x_2797_);
v_a_2785_ = v___x_2791_;
goto v___jp_2784_;
}
}
}
v___jp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = lean_nat_add(v_a_2782_, v___x_2786_);
lean_dec(v_a_2782_);
v_a_2782_ = v___x_2787_;
v_b_2783_ = v_a_2785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2800_, lean_object* v_accept_2801_, lean_object* v_stack_2802_, lean_object* v_stx_2803_){
_start:
{
lean_object* v___x_2804_; uint8_t v___x_2805_; 
lean_inc_ref(v_accept_2801_);
lean_inc(v_stx_2803_);
v___x_2804_ = lean_apply_1(v_accept_2801_, v_stx_2803_);
v___x_2805_ = lean_unbox(v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_fst_2811_; 
v___x_2806_ = l_Lean_Syntax_getNumArgs(v_stx_2803_);
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_box(0);
v___x_2809_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2810_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2806_, v_stx_2803_, v_visit_2800_, v_stack_2802_, v_accept_2801_, v___x_2807_, v___x_2809_);
lean_dec(v___x_2806_);
v_fst_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_fst_2811_);
lean_dec_ref(v___x_2810_);
if (lean_obj_tag(v_fst_2811_) == 0)
{
return v___x_2808_;
}
else
{
lean_object* v_val_2812_; 
v_val_2812_ = lean_ctor_get(v_fst_2811_, 0);
lean_inc(v_val_2812_);
lean_dec_ref_known(v_fst_2811_, 1);
return v_val_2812_;
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec_ref(v_accept_2801_);
lean_dec_ref(v_visit_2800_);
v___x_2813_ = lean_unsigned_to_nat(0u);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_stx_2803_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_stack_2802_);
v___x_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2817_, lean_object* v_stx_2818_, lean_object* v_visit_2819_, lean_object* v_stack_2820_, lean_object* v_accept_2821_, lean_object* v_a_2822_, lean_object* v_b_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2817_, v_stx_2818_, v_visit_2819_, v_stack_2820_, v_accept_2821_, v_a_2822_, v_b_2823_);
lean_dec_ref(v_b_2823_);
lean_dec(v_upperBound_2817_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2825_, lean_object* v_stx_2826_, lean_object* v_visit_2827_, lean_object* v_stack_2828_, lean_object* v_accept_2829_, lean_object* v_inst_2830_, lean_object* v_R_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_, lean_object* v_c_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2825_, v_stx_2826_, v_visit_2827_, v_stack_2828_, v_accept_2829_, v_a_2832_, v_b_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2836_, lean_object* v_stx_2837_, lean_object* v_visit_2838_, lean_object* v_stack_2839_, lean_object* v_accept_2840_, lean_object* v_inst_2841_, lean_object* v_R_2842_, lean_object* v_a_2843_, lean_object* v_b_2844_, lean_object* v_c_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2836_, v_stx_2837_, v_visit_2838_, v_stack_2839_, v_accept_2840_, v_inst_2841_, v_R_2842_, v_a_2843_, v_b_2844_, v_c_2845_);
lean_dec_ref(v_b_2844_);
lean_dec(v_upperBound_2836_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2847_, lean_object* v_visit_2848_, lean_object* v_accept_2849_){
_start:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
lean_inc_ref(v_visit_2848_);
lean_inc(v_root_2847_);
v___x_2850_ = lean_apply_1(v_visit_2848_, v_root_2847_);
v___x_2851_ = lean_unbox(v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec_ref(v_accept_2849_);
lean_dec_ref(v_visit_2848_);
lean_dec(v_root_2847_);
v___x_2852_ = lean_box(0);
return v___x_2852_;
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_box(0);
v___x_2854_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2848_, v_accept_2849_, v___x_2853_, v_root_2847_);
return v___x_2854_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2855_, lean_object* v_x_2856_, lean_object* v_p_2857_){
_start:
{
if (lean_obj_tag(v_p_2857_) == 0)
{
lean_dec_ref(v_x_2856_);
return v___x_2855_;
}
else
{
lean_object* v_fst_2858_; lean_object* v_val_2859_; uint8_t v___x_2860_; 
v_fst_2858_ = lean_ctor_get(v_x_2856_, 0);
lean_inc(v_fst_2858_);
lean_dec_ref(v_x_2856_);
v_val_2859_ = lean_ctor_get(v_p_2857_, 0);
v___x_2860_ = l_Lean_Syntax_isOfKind(v_fst_2858_, v_val_2859_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2861_, lean_object* v_x_2862_, lean_object* v_p_2863_){
_start:
{
uint8_t v___x_123__boxed_2864_; uint8_t v_res_2865_; lean_object* v_r_2866_; 
v___x_123__boxed_2864_ = lean_unbox(v___x_2861_);
v_res_2865_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2864_, v_x_2862_, v_p_2863_);
lean_dec(v_p_2863_);
v_r_2866_ = lean_box(v_res_2865_);
return v_r_2866_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2867_){
_start:
{
if (lean_obj_tag(v_x_2867_) == 0)
{
uint8_t v___x_2868_; 
v___x_2868_ = 1;
return v___x_2868_;
}
else
{
lean_object* v_head_2869_; uint8_t v___x_2870_; 
v_head_2869_ = lean_ctor_get(v_x_2867_, 0);
v___x_2870_ = lean_unbox(v_head_2869_);
if (v___x_2870_ == 0)
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_unbox(v_head_2869_);
return v___x_2871_;
}
else
{
lean_object* v_tail_2872_; 
v_tail_2872_ = lean_ctor_get(v_x_2867_, 1);
v_x_2867_ = v_tail_2872_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2874_){
_start:
{
uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_res_2875_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2874_);
lean_dec(v_x_2874_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2879_, lean_object* v_pattern_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2881_ = l_List_lengthTR___redArg(v_pattern_2880_);
v___x_2882_ = l_List_lengthTR___redArg(v_stack_2879_);
v___x_2883_ = lean_nat_dec_le(v___x_2881_, v___x_2882_);
lean_dec(v___x_2882_);
lean_dec(v___x_2881_);
if (v___x_2883_ == 0)
{
lean_dec(v_pattern_2880_);
lean_dec(v_stack_2879_);
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v___x_2884_ = lean_box(v___x_2883_);
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2885_, 0, v___x_2884_);
v___x_2886_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2887_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2885_, v_stack_2879_, v_pattern_2880_, v___x_2886_);
v___x_2888_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2887_);
lean_dec(v___x_2887_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2889_, lean_object* v_pattern_2890_){
_start:
{
uint8_t v_res_2891_; lean_object* v_r_2892_; 
v_res_2891_ = l_Lean_Syntax_Stack_matches(v_stack_2889_, v_pattern_2890_);
v_r_2892_ = lean_box(v_res_2891_);
return v_r_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2893_, lean_object* v_trailing_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2893_);
if (lean_obj_tag(v___x_2895_) == 1)
{
lean_object* v_val_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2931_; 
v_val_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2931_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_val_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2931_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
if (lean_obj_tag(v_val_2896_) == 0)
{
lean_object* v_trailing_2900_; lean_object* v_leading_2901_; lean_object* v_pos_2902_; lean_object* v_endPos_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2929_; 
v_trailing_2900_ = lean_ctor_get(v_val_2896_, 2);
v_leading_2901_ = lean_ctor_get(v_val_2896_, 0);
v_pos_2902_ = lean_ctor_get(v_val_2896_, 1);
v_endPos_2903_ = lean_ctor_get(v_val_2896_, 3);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_val_2896_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2905_ = v_val_2896_;
v_isShared_2906_ = v_isSharedCheck_2929_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_endPos_2903_);
lean_inc(v_trailing_2900_);
lean_inc(v_pos_2902_);
lean_inc(v_leading_2901_);
lean_dec(v_val_2896_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2929_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_str_2907_; lean_object* v_startPos_2908_; lean_object* v_stopPos_2909_; lean_object* v_startPos_2910_; lean_object* v_stopPos_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2927_; 
v_str_2907_ = lean_ctor_get(v_trailing_2900_, 0);
lean_inc_ref(v_str_2907_);
v_startPos_2908_ = lean_ctor_get(v_trailing_2900_, 1);
lean_inc(v_startPos_2908_);
v_stopPos_2909_ = lean_ctor_get(v_trailing_2900_, 2);
lean_inc(v_stopPos_2909_);
lean_dec_ref(v_trailing_2900_);
v_startPos_2910_ = lean_ctor_get(v_trailing_2894_, 1);
v_stopPos_2911_ = lean_ctor_get(v_trailing_2894_, 2);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_trailing_2894_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v_trailing_2894_, 0);
lean_dec(v_unused_2928_);
v___x_2913_ = v_trailing_2894_;
v_isShared_2914_ = v_isSharedCheck_2927_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_stopPos_2911_);
lean_inc(v_startPos_2910_);
lean_dec(v_trailing_2894_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2927_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v_decide_2915_; 
v_decide_2915_ = lean_nat_dec_eq(v_stopPos_2909_, v_startPos_2910_);
lean_dec(v_startPos_2910_);
lean_dec(v_stopPos_2909_);
if (v_decide_2915_ == 0)
{
lean_object* v___x_2916_; 
lean_del_object(v___x_2913_);
lean_dec(v_stopPos_2911_);
lean_dec(v_startPos_2908_);
lean_dec_ref(v_str_2907_);
lean_del_object(v___x_2905_);
lean_dec(v_endPos_2903_);
lean_dec(v_pos_2902_);
lean_dec_ref(v_leading_2901_);
lean_del_object(v___x_2898_);
lean_dec(v_stx_2893_);
v___x_2916_ = lean_box(0);
return v___x_2916_;
}
else
{
lean_object* v_trailing_2918_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v_startPos_2908_);
lean_ctor_set(v___x_2913_, 0, v_str_2907_);
v_trailing_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_str_2907_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_startPos_2908_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_stopPos_2911_);
v_trailing_2918_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 2, v_trailing_2918_);
v___x_2920_ = v___x_2905_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_leading_2901_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_pos_2902_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_trailing_2918_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_endPos_2903_);
v___x_2920_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2921_ = l_Lean_Syntax_setTailInfo(v_stx_2893_, v___x_2920_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2921_);
v___x_2923_ = v___x_2898_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2930_; 
lean_del_object(v___x_2898_);
lean_dec(v_val_2896_);
lean_dec_ref(v_trailing_2894_);
lean_dec(v_stx_2893_);
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
}
}
else
{
lean_object* v___x_2932_; 
lean_dec(v___x_2895_);
lean_dec_ref(v_trailing_2894_);
lean_dec(v_stx_2893_);
v___x_2932_ = lean_box(0);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2933_, lean_object* v_trailing_2934_){
_start:
{
lean_object* v___x_2935_; 
lean_inc(v_stx_2933_);
v___x_2935_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2933_, v_trailing_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
return v_stx_2933_;
}
else
{
lean_object* v_val_2936_; 
lean_dec(v_stx_2933_);
v_val_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_val_2936_);
lean_dec_ref_known(v___x_2935_, 1);
return v_val_2936_;
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

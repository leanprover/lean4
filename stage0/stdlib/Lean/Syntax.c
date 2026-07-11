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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
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
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_start_138_; lean_object* v_stop_139_; lean_object* v_start_140_; lean_object* v_stop_141_; uint8_t v___y_143_; uint8_t v___x_148_; 
v_start_138_ = lean_ctor_get(v_super_134_, 0);
v_stop_139_ = lean_ctor_get(v_super_134_, 1);
v_start_140_ = lean_ctor_get(v_sub_135_, 0);
v_stop_141_ = lean_ctor_get(v_sub_135_, 1);
v___x_148_ = lean_nat_dec_le(v_start_138_, v_start_140_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
if (v_includeSuperStop_136_ == 0)
{
goto v___jp_146_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_bool_not(v_includeSubStop_137_);
if (v___x_149_ == 0)
{
goto v___jp_146_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_stop_139_, v___x_150_);
v___x_152_ = lean_nat_dec_le(v_stop_141_, v___x_151_);
lean_dec(v___x_151_);
return v___x_152_;
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
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_lt(v_stop_141_, v_stop_139_);
return v___x_145_;
}
}
v___jp_146_:
{
uint8_t v___x_147_; 
v___x_147_ = lean_bool_not(v_includeSuperStop_136_);
if (v___x_147_ == 0)
{
v___y_143_ = v___x_147_;
goto v___jp_142_;
}
else
{
v___y_143_ = v_includeSubStop_137_;
goto v___jp_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_153_, lean_object* v_sub_154_, lean_object* v_includeSuperStop_155_, lean_object* v_includeSubStop_156_){
_start:
{
uint8_t v_includeSuperStop_boxed_157_; uint8_t v_includeSubStop_boxed_158_; uint8_t v_res_159_; lean_object* v_r_160_; 
v_includeSuperStop_boxed_157_ = lean_unbox(v_includeSuperStop_155_);
v_includeSubStop_boxed_158_ = lean_unbox(v_includeSubStop_156_);
v_res_159_ = l_Lean_Syntax_Range_includes(v_super_153_, v_sub_154_, v_includeSuperStop_boxed_157_, v_includeSubStop_boxed_158_);
lean_dec_ref(v_sub_154_);
lean_dec_ref(v_super_153_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_161_, lean_object* v_second_162_, uint8_t v_includeFirstStop_163_, uint8_t v_includeSecondStop_164_){
_start:
{
uint8_t v___y_166_; 
if (v_includeFirstStop_163_ == 0)
{
lean_object* v_start_173_; lean_object* v_stop_174_; uint8_t v___x_175_; 
v_start_173_ = lean_ctor_get(v_second_162_, 0);
v_stop_174_ = lean_ctor_get(v_first_161_, 1);
v___x_175_ = lean_nat_dec_lt(v_start_173_, v_stop_174_);
v___y_166_ = v___x_175_;
goto v___jp_165_;
}
else
{
lean_object* v_start_176_; lean_object* v_stop_177_; uint8_t v___x_178_; 
v_start_176_ = lean_ctor_get(v_second_162_, 0);
v_stop_177_ = lean_ctor_get(v_first_161_, 1);
v___x_178_ = lean_nat_dec_le(v_start_176_, v_stop_177_);
v___y_166_ = v___x_178_;
goto v___jp_165_;
}
v___jp_165_:
{
if (v___y_166_ == 0)
{
return v___y_166_;
}
else
{
if (v_includeSecondStop_164_ == 0)
{
lean_object* v_start_167_; lean_object* v_stop_168_; uint8_t v___x_169_; 
v_start_167_ = lean_ctor_get(v_first_161_, 0);
v_stop_168_ = lean_ctor_get(v_second_162_, 1);
v___x_169_ = lean_nat_dec_lt(v_start_167_, v_stop_168_);
return v___x_169_;
}
else
{
lean_object* v_start_170_; lean_object* v_stop_171_; uint8_t v___x_172_; 
v_start_170_ = lean_ctor_get(v_first_161_, 0);
v_stop_171_ = lean_ctor_get(v_second_162_, 1);
v___x_172_ = lean_nat_dec_le(v_start_170_, v_stop_171_);
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object* v_first_179_, lean_object* v_second_180_, lean_object* v_includeFirstStop_181_, lean_object* v_includeSecondStop_182_){
_start:
{
uint8_t v_includeFirstStop_boxed_183_; uint8_t v_includeSecondStop_boxed_184_; uint8_t v_res_185_; lean_object* v_r_186_; 
v_includeFirstStop_boxed_183_ = lean_unbox(v_includeFirstStop_181_);
v_includeSecondStop_boxed_184_ = lean_unbox(v_includeSecondStop_182_);
v_res_185_ = l_Lean_Syntax_Range_overlaps(v_first_179_, v_second_180_, v_includeFirstStop_boxed_183_, v_includeSecondStop_boxed_184_);
lean_dec_ref(v_second_180_);
lean_dec_ref(v_first_179_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_187_){
_start:
{
lean_object* v_start_188_; lean_object* v_stop_189_; lean_object* v___x_190_; 
v_start_188_ = lean_ctor_get(v_r_187_, 0);
v_stop_189_ = lean_ctor_get(v_r_187_, 1);
v___x_190_ = lean_nat_sub(v_stop_189_, v_start_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Syntax_Range_bsize(v_r_191_);
lean_dec_ref(v_r_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_193_, lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v_leading_195_; lean_object* v_pos_196_; lean_object* v_endPos_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_leading_195_ = lean_ctor_get(v_x_194_, 0);
v_pos_196_ = lean_ctor_get(v_x_194_, 1);
v_endPos_197_ = lean_ctor_get(v_x_194_, 3);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_x_194_, 2);
lean_dec(v_unused_205_);
v___x_199_ = v_x_194_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_endPos_197_);
lean_inc(v_pos_196_);
lean_inc(v_leading_195_);
lean_dec(v_x_194_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 2, v_trailing_193_);
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_leading_195_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_pos_196_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_trailing_193_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_endPos_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_dec_ref(v_trailing_193_);
return v_x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_206_, lean_object* v_info_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_SourceInfo_getPos_x3f(v_info_207_, v_canonicalOnly_206_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; 
v_val_210_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_208_, 1);
v___x_211_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_207_, v_canonicalOnly_206_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; 
lean_dec(v_val_210_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v_val_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_221_; 
v_val_213_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_221_ == 0)
{
v___x_215_ = v___x_211_;
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_val_213_);
lean_dec(v___x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_val_210_);
lean_ctor_set(v___x_217_, 1, v_val_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_222_, lean_object* v_info_223_){
_start:
{
uint8_t v_canonicalOnly_boxed_224_; lean_object* v_res_225_; 
v_canonicalOnly_boxed_224_ = lean_unbox(v_canonicalOnly_222_);
v_res_225_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_224_, v_info_223_);
lean_dec(v_info_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_226_, lean_object* v_info_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_SourceInfo_getPos_x3f(v_info_227_, v_canonicalOnly_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_228_, 1);
v___x_231_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_227_, v_canonicalOnly_226_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
lean_dec(v_val_230_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_val_230_);
lean_ctor_set(v___x_237_, 1, v_val_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_242_, lean_object* v_info_243_){
_start:
{
uint8_t v_canonicalOnly_boxed_244_; lean_object* v_res_245_; 
v_canonicalOnly_boxed_244_ = lean_unbox(v_canonicalOnly_242_);
v_res_245_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_244_, v_info_243_);
lean_dec(v_info_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_246_){
_start:
{
switch(lean_obj_tag(v_x_246_))
{
case 0:
{
lean_object* v_pos_247_; lean_object* v_endPos_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v_pos_247_ = lean_ctor_get(v_x_246_, 1);
lean_inc(v_pos_247_);
v_endPos_248_ = lean_ctor_get(v_x_246_, 3);
lean_inc(v_endPos_248_);
lean_dec_ref_known(v_x_246_, 4);
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_250_, 0, v_pos_247_);
lean_ctor_set(v___x_250_, 1, v_endPos_248_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*2, v___x_249_);
return v___x_250_;
}
case 1:
{
lean_object* v_pos_251_; lean_object* v_endPos_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_pos_251_ = lean_ctor_get(v_x_246_, 0);
v_endPos_252_ = lean_ctor_get(v_x_246_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v_x_246_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_endPos_252_);
lean_inc(v_pos_251_);
lean_dec(v_x_246_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; lean_object* v___x_258_; 
v___x_256_ = 0;
if (v_isShared_255_ == 0)
{
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_pos_251_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_endPos_252_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*2, v___x_256_);
return v___x_258_;
}
}
}
default: 
{
return v_x_246_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
switch(lean_obj_tag(v_x_261_))
{
case 0:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v_leading_263_; lean_object* v_pos_264_; lean_object* v_trailing_265_; lean_object* v_endPos_266_; lean_object* v_leading_267_; lean_object* v_pos_268_; lean_object* v_trailing_269_; lean_object* v_endPos_270_; uint8_t v___x_271_; 
v_leading_263_ = lean_ctor_get(v_x_261_, 0);
lean_inc_ref(v_leading_263_);
v_pos_264_ = lean_ctor_get(v_x_261_, 1);
lean_inc(v_pos_264_);
v_trailing_265_ = lean_ctor_get(v_x_261_, 2);
lean_inc_ref(v_trailing_265_);
v_endPos_266_ = lean_ctor_get(v_x_261_, 3);
lean_inc(v_endPos_266_);
lean_dec_ref_known(v_x_261_, 4);
v_leading_267_ = lean_ctor_get(v_x_262_, 0);
lean_inc_ref(v_leading_267_);
v_pos_268_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_pos_268_);
v_trailing_269_ = lean_ctor_get(v_x_262_, 2);
lean_inc_ref(v_trailing_269_);
v_endPos_270_ = lean_ctor_get(v_x_262_, 3);
lean_inc(v_endPos_270_);
lean_dec_ref_known(v_x_262_, 4);
v___x_271_ = l_Substring_Raw_beq(v_leading_263_, v_leading_267_);
if (v___x_271_ == 0)
{
lean_dec(v_endPos_270_);
lean_dec_ref(v_trailing_269_);
lean_dec(v_pos_268_);
lean_dec(v_endPos_266_);
lean_dec_ref(v_trailing_265_);
lean_dec(v_pos_264_);
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_eq(v_pos_264_, v_pos_268_);
lean_dec(v_pos_268_);
lean_dec(v_pos_264_);
if (v___x_272_ == 0)
{
lean_dec(v_endPos_270_);
lean_dec_ref(v_trailing_269_);
lean_dec(v_endPos_266_);
lean_dec_ref(v_trailing_265_);
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = l_Substring_Raw_beq(v_trailing_265_, v_trailing_269_);
if (v___x_273_ == 0)
{
lean_dec(v_endPos_270_);
lean_dec(v_endPos_266_);
return v___x_273_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_eq(v_endPos_266_, v_endPos_270_);
lean_dec(v_endPos_270_);
lean_dec(v_endPos_266_);
return v___x_274_;
}
}
}
}
else
{
uint8_t v___x_275_; 
lean_dec_ref_known(v_x_261_, 4);
lean_dec(v_x_262_);
v___x_275_ = 0;
return v___x_275_;
}
}
case 1:
{
if (lean_obj_tag(v_x_262_) == 1)
{
lean_object* v_pos_276_; lean_object* v_endPos_277_; uint8_t v_canonical_278_; lean_object* v_pos_279_; lean_object* v_endPos_280_; uint8_t v_canonical_281_; uint8_t v___x_282_; 
v_pos_276_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_pos_276_);
v_endPos_277_ = lean_ctor_get(v_x_261_, 1);
lean_inc(v_endPos_277_);
v_canonical_278_ = lean_ctor_get_uint8(v_x_261_, sizeof(void*)*2);
lean_dec_ref_known(v_x_261_, 2);
v_pos_279_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_pos_279_);
v_endPos_280_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_endPos_280_);
v_canonical_281_ = lean_ctor_get_uint8(v_x_262_, sizeof(void*)*2);
lean_dec_ref_known(v_x_262_, 2);
v___x_282_ = lean_nat_dec_eq(v_pos_276_, v_pos_279_);
lean_dec(v_pos_279_);
lean_dec(v_pos_276_);
if (v___x_282_ == 0)
{
lean_dec(v_endPos_280_);
lean_dec(v_endPos_277_);
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = lean_nat_dec_eq(v_endPos_277_, v_endPos_280_);
lean_dec(v_endPos_280_);
lean_dec(v_endPos_277_);
if (v___x_283_ == 0)
{
return v___x_283_;
}
else
{
if (v_canonical_278_ == 0)
{
if (v_canonical_281_ == 0)
{
return v___x_283_;
}
else
{
return v_canonical_278_;
}
}
else
{
return v_canonical_281_;
}
}
}
}
else
{
uint8_t v___x_284_; 
lean_dec_ref_known(v_x_261_, 2);
lean_dec(v_x_262_);
v___x_284_ = 0;
return v___x_284_;
}
}
default: 
{
if (lean_obj_tag(v_x_262_) == 2)
{
uint8_t v___x_285_; 
v___x_285_ = 1;
return v___x_285_;
}
else
{
uint8_t v___x_286_; 
lean_dec(v_x_262_);
v___x_286_ = 0;
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_287_, v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_293_, lean_object* v_a_294_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_295_, lean_object* v_info_296_, lean_object* v_val_297_, lean_object* v_a_298_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_299_, lean_object* v_info_300_, lean_object* v_val_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_299_, v_info_300_, v_val_301_, v_a_302_);
lean_dec_ref(v_val_301_);
lean_dec(v_info_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_304_, lean_object* v_info_305_, lean_object* v_rawVal_306_, lean_object* v_val_307_, lean_object* v_preresolved_308_, lean_object* v_a_309_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_310_, lean_object* v_info_311_, lean_object* v_rawVal_312_, lean_object* v_val_313_, lean_object* v_preresolved_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_310_, v_info_311_, v_rawVal_312_, v_val_313_, v_preresolved_314_, v_a_315_);
lean_dec(v_preresolved_314_);
lean_dec(v_val_313_);
lean_dec_ref(v_rawVal_312_);
lean_dec(v_info_311_);
return v_res_316_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object* v_k_332_){
_start:
{
uint8_t v___y_334_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_342_ = lean_name_eq(v_k_332_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_344_ = lean_name_eq(v_k_332_, v___x_343_);
v___y_334_ = v___x_344_;
goto v___jp_333_;
}
else
{
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
v___jp_333_:
{
if (v___y_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_336_ = lean_name_eq(v_k_332_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_338_ = lean_name_eq(v_k_332_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_340_ = lean_name_eq(v_k_332_, v___x_339_);
return v___x_340_;
}
else
{
return v___x_338_;
}
}
else
{
return v___x_336_;
}
}
else
{
return v___y_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Lean_isLitKind(v_k_345_);
lean_dec(v_k_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_348_){
_start:
{
lean_object* v_kind_349_; 
v_kind_349_ = lean_ctor_get(v_n_348_, 1);
lean_inc(v_kind_349_);
return v_kind_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_SyntaxNode_getKind(v_n_350_);
lean_dec(v_n_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_352_, lean_object* v_fn_353_){
_start:
{
lean_object* v_args_354_; lean_object* v___x_355_; 
v_args_354_ = lean_ctor_get(v_n_352_, 2);
lean_inc_ref(v_args_354_);
lean_dec(v_n_352_);
v___x_355_ = lean_apply_1(v_fn_353_, v_args_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_356_, lean_object* v_n_357_, lean_object* v_fn_358_){
_start:
{
lean_object* v_args_359_; lean_object* v___x_360_; 
v_args_359_ = lean_ctor_get(v_n_357_, 2);
lean_inc_ref(v_args_359_);
lean_dec(v_n_357_);
v___x_360_ = lean_apply_1(v_fn_358_, v_args_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_361_){
_start:
{
lean_object* v_args_362_; lean_object* v___x_363_; 
v_args_362_ = lean_ctor_get(v_n_361_, 2);
v___x_363_ = lean_array_get_size(v_args_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_SyntaxNode_getNumArgs(v_n_364_);
lean_dec(v_n_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_366_, lean_object* v_i_367_){
_start:
{
lean_object* v_args_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_args_368_ = lean_ctor_get(v_n_366_, 2);
v___x_369_ = lean_box(0);
v___x_370_ = lean_array_get_borrowed(v___x_369_, v_args_368_, v_i_367_);
lean_inc(v___x_370_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_371_, lean_object* v_i_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_SyntaxNode_getArg(v_n_371_, v_i_372_);
lean_dec(v_i_372_);
lean_dec(v_n_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_374_){
_start:
{
lean_object* v_args_375_; 
v_args_375_ = lean_ctor_get(v_n_374_, 2);
lean_inc_ref(v_args_375_);
return v_args_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_SyntaxNode_getArgs(v_n_376_);
lean_dec(v_n_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_378_, lean_object* v_fn_379_){
_start:
{
lean_object* v_info_380_; lean_object* v_kind_381_; lean_object* v_args_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_info_380_ = lean_ctor_get(v_n_378_, 0);
v_kind_381_ = lean_ctor_get(v_n_378_, 1);
v_args_382_ = lean_ctor_get(v_n_378_, 2);
v_isSharedCheck_390_ = !lean_is_exclusive(v_n_378_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v_n_378_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_args_382_);
lean_inc(v_kind_381_);
lean_inc(v_info_380_);
lean_dec(v_n_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_apply_1(v_fn_379_, v_args_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 2, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_info_380_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_kind_381_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
if (lean_obj_tag(v_x_392_) == 0)
{
uint8_t v___x_393_; 
v___x_393_ = 1;
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
}
else
{
if (lean_obj_tag(v_x_392_) == 0)
{
uint8_t v___x_395_; 
v___x_395_ = 0;
return v___x_395_;
}
else
{
lean_object* v_val_396_; lean_object* v_val_397_; uint8_t v___x_398_; 
v_val_396_ = lean_ctor_get(v_x_391_, 0);
v_val_397_ = lean_ctor_get(v_x_392_, 0);
v___x_398_ = l_Lean_Syntax_instBEqRange_beq(v_val_396_, v_val_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_399_, v_x_400_);
lean_dec(v_x_400_);
lean_dec(v_x_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
if (lean_obj_tag(v_x_404_) == 0)
{
uint8_t v___x_405_; 
v___x_405_ = 1;
return v___x_405_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = 0;
return v___x_406_;
}
}
else
{
if (lean_obj_tag(v_x_404_) == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
else
{
lean_object* v_head_408_; lean_object* v_tail_409_; lean_object* v_head_410_; lean_object* v_tail_411_; uint8_t v___x_412_; 
v_head_408_ = lean_ctor_get(v_x_403_, 0);
v_tail_409_ = lean_ctor_get(v_x_403_, 1);
v_head_410_ = lean_ctor_get(v_x_404_, 0);
v_tail_411_ = lean_ctor_get(v_x_404_, 1);
v___x_412_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_408_, v_head_410_);
if (v___x_412_ == 0)
{
return v___x_412_;
}
else
{
v_x_403_ = v_tail_409_;
v_x_404_ = v_tail_411_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
switch(lean_obj_tag(v_x_418_))
{
case 0:
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
lean_dec(v_x_419_);
v___x_421_ = 0;
return v___x_421_;
}
}
case 1:
{
if (lean_obj_tag(v_x_419_) == 1)
{
lean_object* v_info_422_; lean_object* v_kind_423_; lean_object* v_args_424_; lean_object* v_info_425_; lean_object* v_kind_426_; lean_object* v_args_427_; uint8_t v___y_429_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_info_422_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_info_422_);
v_kind_423_ = lean_ctor_get(v_x_418_, 1);
lean_inc(v_kind_423_);
v_args_424_ = lean_ctor_get(v_x_418_, 2);
lean_inc_ref(v_args_424_);
lean_dec_ref_known(v_x_418_, 3);
v_info_425_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_info_425_);
v_kind_426_ = lean_ctor_get(v_x_419_, 1);
lean_inc(v_kind_426_);
v_args_427_ = lean_ctor_get(v_x_419_, 2);
lean_inc_ref(v_args_427_);
lean_dec_ref_known(v_x_419_, 3);
v___x_434_ = 0;
v___x_435_ = l_Lean_SourceInfo_getRange_x3f(v___x_434_, v_info_422_);
lean_dec(v_info_422_);
v___x_436_ = l_Lean_SourceInfo_getRange_x3f(v___x_434_, v_info_425_);
lean_dec(v_info_425_);
v___x_437_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_435_, v___x_436_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
if (v___x_437_ == 0)
{
lean_dec(v_kind_426_);
lean_dec(v_kind_423_);
v___y_429_ = v___x_437_;
goto v___jp_428_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = lean_name_eq(v_kind_423_, v_kind_426_);
lean_dec(v_kind_426_);
lean_dec(v_kind_423_);
v___y_429_ = v___x_438_;
goto v___jp_428_;
}
v___jp_428_:
{
if (v___y_429_ == 0)
{
lean_dec_ref(v_args_427_);
lean_dec_ref(v_args_424_);
return v___y_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = lean_array_get_size(v_args_424_);
v___x_431_ = lean_array_get_size(v_args_427_);
v___x_432_ = lean_nat_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_dec_ref(v_args_427_);
lean_dec_ref(v_args_424_);
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_args_424_, v_args_427_, v___x_430_);
lean_dec_ref(v_args_427_);
lean_dec_ref(v_args_424_);
return v___x_433_;
}
}
}
}
else
{
uint8_t v___x_439_; 
lean_dec_ref_known(v_x_418_, 3);
lean_dec(v_x_419_);
v___x_439_ = 0;
return v___x_439_;
}
}
case 2:
{
if (lean_obj_tag(v_x_419_) == 2)
{
lean_object* v_info_440_; lean_object* v_val_441_; lean_object* v_info_442_; lean_object* v_val_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_info_440_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_info_440_);
v_val_441_ = lean_ctor_get(v_x_418_, 1);
lean_inc_ref(v_val_441_);
lean_dec_ref_known(v_x_418_, 2);
v_info_442_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_info_442_);
v_val_443_ = lean_ctor_get(v_x_419_, 1);
lean_inc_ref(v_val_443_);
lean_dec_ref_known(v_x_419_, 2);
v___x_444_ = 0;
v___x_445_ = l_Lean_SourceInfo_getRange_x3f(v___x_444_, v_info_440_);
lean_dec(v_info_440_);
v___x_446_ = l_Lean_SourceInfo_getRange_x3f(v___x_444_, v_info_442_);
lean_dec(v_info_442_);
v___x_447_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_445_, v___x_446_);
lean_dec(v___x_446_);
lean_dec(v___x_445_);
if (v___x_447_ == 0)
{
lean_dec_ref(v_val_443_);
lean_dec_ref(v_val_441_);
return v___x_447_;
}
else
{
uint8_t v___x_448_; 
v___x_448_ = lean_string_dec_eq(v_val_441_, v_val_443_);
lean_dec_ref(v_val_443_);
lean_dec_ref(v_val_441_);
return v___x_448_;
}
}
else
{
uint8_t v___x_449_; 
lean_dec_ref_known(v_x_418_, 2);
lean_dec(v_x_419_);
v___x_449_ = 0;
return v___x_449_;
}
}
default: 
{
if (lean_obj_tag(v_x_419_) == 3)
{
lean_object* v_info_450_; lean_object* v_rawVal_451_; lean_object* v_val_452_; lean_object* v_preresolved_453_; lean_object* v_info_454_; lean_object* v_rawVal_455_; lean_object* v_val_456_; lean_object* v_preresolved_457_; uint8_t v___y_459_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_info_450_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_info_450_);
v_rawVal_451_ = lean_ctor_get(v_x_418_, 1);
lean_inc_ref(v_rawVal_451_);
v_val_452_ = lean_ctor_get(v_x_418_, 2);
lean_inc(v_val_452_);
v_preresolved_453_ = lean_ctor_get(v_x_418_, 3);
lean_inc(v_preresolved_453_);
lean_dec_ref_known(v_x_418_, 4);
v_info_454_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_info_454_);
v_rawVal_455_ = lean_ctor_get(v_x_419_, 1);
lean_inc_ref(v_rawVal_455_);
v_val_456_ = lean_ctor_get(v_x_419_, 2);
lean_inc(v_val_456_);
v_preresolved_457_ = lean_ctor_get(v_x_419_, 3);
lean_inc(v_preresolved_457_);
lean_dec_ref_known(v_x_419_, 4);
v___x_462_ = 0;
v___x_463_ = l_Lean_SourceInfo_getRange_x3f(v___x_462_, v_info_450_);
lean_dec(v_info_450_);
v___x_464_ = l_Lean_SourceInfo_getRange_x3f(v___x_462_, v_info_454_);
lean_dec(v_info_454_);
v___x_465_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_463_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_463_);
if (v___x_465_ == 0)
{
lean_dec_ref(v_rawVal_455_);
lean_dec_ref(v_rawVal_451_);
v___y_459_ = v___x_465_;
goto v___jp_458_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = l_Substring_Raw_beq(v_rawVal_451_, v_rawVal_455_);
v___y_459_ = v___x_466_;
goto v___jp_458_;
}
v___jp_458_:
{
if (v___y_459_ == 0)
{
lean_dec(v_preresolved_457_);
lean_dec(v_val_456_);
lean_dec(v_preresolved_453_);
lean_dec(v_val_452_);
return v___y_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = lean_name_eq(v_val_452_, v_val_456_);
lean_dec(v_val_456_);
lean_dec(v_val_452_);
if (v___x_460_ == 0)
{
lean_dec(v_preresolved_457_);
lean_dec(v_preresolved_453_);
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_453_, v_preresolved_457_);
lean_dec(v_preresolved_457_);
lean_dec(v_preresolved_453_);
return v___x_461_;
}
}
}
}
else
{
uint8_t v___x_467_; 
lean_dec_ref_known(v_x_418_, 4);
lean_dec(v_x_419_);
v___x_467_ = 0;
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object* v_xs_468_, lean_object* v_ys_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_zero_471_; uint8_t v_isZero_472_; 
v_zero_471_ = lean_unsigned_to_nat(0u);
v_isZero_472_ = lean_nat_dec_eq(v_x_470_, v_zero_471_);
if (v_isZero_472_ == 1)
{
lean_dec(v_x_470_);
return v_isZero_472_;
}
else
{
lean_object* v_one_473_; lean_object* v_n_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_one_473_ = lean_unsigned_to_nat(1u);
v_n_474_ = lean_nat_sub(v_x_470_, v_one_473_);
lean_dec(v_x_470_);
v___x_475_ = lean_array_fget_borrowed(v_xs_468_, v_n_474_);
v___x_476_ = lean_array_fget_borrowed(v_ys_469_, v_n_474_);
lean_inc(v___x_476_);
lean_inc(v___x_475_);
v___x_477_ = l_Lean_Syntax_structRangeEq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v_n_474_);
return v___x_477_;
}
else
{
v_x_470_ = v_n_474_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object* v_xs_479_, lean_object* v_ys_480_, lean_object* v_x_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_479_, v_ys_480_, v_x_481_);
lean_dec_ref(v_ys_480_);
lean_dec_ref(v_xs_479_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Lean_Syntax_structRangeEq(v_x_484_, v_x_485_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_xs_488_, lean_object* v_ys_489_, lean_object* v_hsz_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_488_, v_ys_489_, v_x_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_xs_494_, lean_object* v_ys_495_, lean_object* v_hsz_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_494_, v_ys_495_, v_hsz_496_, v_x_497_, v_x_498_);
lean_dec_ref(v_ys_495_);
lean_dec_ref(v_xs_494_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_501_, lean_object* v_x_502_){
_start:
{
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_503_, lean_object* v_x_504_){
_start:
{
uint8_t v___x_207__boxed_505_; uint8_t v_res_506_; lean_object* v_r_507_; 
v___x_207__boxed_505_ = lean_unbox(v___x_503_);
v_res_506_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_207__boxed_505_, v_x_504_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_517_, lean_object* v_stx1_518_, lean_object* v_stx2_519_){
_start:
{
uint8_t v___x_520_; uint8_t v___x_521_; 
lean_inc(v_stx2_519_);
lean_inc(v_stx1_518_);
v___x_520_ = l_Lean_Syntax_structRangeEq(v_stx1_518_, v_stx2_519_);
v___x_521_ = 1;
if (v___x_520_ == 0)
{
lean_object* v_map_522_; lean_object* v___x_523_; lean_object* v___f_524_; uint8_t v___y_526_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_map_522_ = lean_ctor_get(v_opts_517_, 0);
v___x_523_ = lean_box(v___x_520_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_524_, 0, v___x_523_);
v___x_541_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_542_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_522_, v___x_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
v___y_526_ = v___x_520_;
goto v___jp_525_;
}
else
{
lean_object* v_val_543_; 
v_val_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v___x_542_, 1);
if (lean_obj_tag(v_val_543_) == 1)
{
uint8_t v_v_544_; 
v_v_544_ = lean_ctor_get_uint8(v_val_543_, 0);
lean_dec_ref_known(v_val_543_, 0);
v___y_526_ = v_v_544_;
goto v___jp_525_;
}
else
{
lean_dec(v_val_543_);
v___y_526_ = v___x_520_;
goto v___jp_525_;
}
}
v___jp_525_:
{
if (v___y_526_ == 0)
{
lean_dec_ref(v___f_524_);
lean_dec(v_stx2_519_);
lean_dec(v_stx1_518_);
return v___x_520_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_527_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_528_ = lean_box(0);
v___x_529_ = l_Lean_Syntax_formatStx(v_stx1_518_, v___x_528_, v___x_521_);
v___x_530_ = l_Std_Format_defWidth;
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l_Std_Format_pretty(v___x_529_, v___x_530_, v___x_531_, v___x_531_);
v___x_533_ = lean_string_append(v___x_527_, v___x_532_);
lean_dec_ref(v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_535_ = lean_string_append(v___x_533_, v___x_534_);
v___x_536_ = l_Lean_Syntax_formatStx(v_stx2_519_, v___x_528_, v___x_521_);
v___x_537_ = l_Std_Format_pretty(v___x_536_, v___x_530_, v___x_531_, v___x_531_);
v___x_538_ = lean_string_append(v___x_535_, v___x_537_);
lean_dec_ref(v___x_537_);
v___x_539_ = lean_dbg_trace(v___x_538_, v___f_524_);
v___x_540_ = lean_unbox(v___x_539_);
lean_dec(v___x_539_);
return v___x_540_;
}
}
}
else
{
lean_dec(v_stx2_519_);
lean_dec(v_stx1_518_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_545_, lean_object* v_stx1_546_, lean_object* v_stx2_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_545_, v_stx1_546_, v_stx2_547_);
lean_dec_ref(v_opts_545_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
switch(lean_obj_tag(v_x_550_))
{
case 0:
{
if (lean_obj_tag(v_x_551_) == 0)
{
uint8_t v___x_552_; 
v___x_552_ = 1;
return v___x_552_;
}
else
{
uint8_t v___x_553_; 
lean_dec(v_x_551_);
v___x_553_ = 0;
return v___x_553_;
}
}
case 1:
{
if (lean_obj_tag(v_x_551_) == 1)
{
lean_object* v_info_554_; lean_object* v_kind_555_; lean_object* v_args_556_; lean_object* v_info_557_; lean_object* v_kind_558_; lean_object* v_args_559_; uint8_t v___y_561_; uint8_t v___x_566_; 
v_info_554_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_info_554_);
v_kind_555_ = lean_ctor_get(v_x_550_, 1);
lean_inc(v_kind_555_);
v_args_556_ = lean_ctor_get(v_x_550_, 2);
lean_inc_ref(v_args_556_);
lean_dec_ref_known(v_x_550_, 3);
v_info_557_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_info_557_);
v_kind_558_ = lean_ctor_get(v_x_551_, 1);
lean_inc(v_kind_558_);
v_args_559_ = lean_ctor_get(v_x_551_, 2);
lean_inc_ref(v_args_559_);
lean_dec_ref_known(v_x_551_, 3);
v___x_566_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_554_, v_info_557_);
if (v___x_566_ == 0)
{
lean_dec(v_kind_558_);
lean_dec(v_kind_555_);
v___y_561_ = v___x_566_;
goto v___jp_560_;
}
else
{
uint8_t v___x_567_; 
v___x_567_ = lean_name_eq(v_kind_555_, v_kind_558_);
lean_dec(v_kind_558_);
lean_dec(v_kind_555_);
v___y_561_ = v___x_567_;
goto v___jp_560_;
}
v___jp_560_:
{
if (v___y_561_ == 0)
{
lean_dec_ref(v_args_559_);
lean_dec_ref(v_args_556_);
return v___y_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = lean_array_get_size(v_args_556_);
v___x_563_ = lean_array_get_size(v_args_559_);
v___x_564_ = lean_nat_dec_eq(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec_ref(v_args_559_);
lean_dec_ref(v_args_556_);
return v___x_564_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_556_, v_args_559_, v___x_562_);
lean_dec_ref(v_args_559_);
lean_dec_ref(v_args_556_);
return v___x_565_;
}
}
}
}
else
{
uint8_t v___x_568_; 
lean_dec_ref_known(v_x_550_, 3);
lean_dec(v_x_551_);
v___x_568_ = 0;
return v___x_568_;
}
}
case 2:
{
if (lean_obj_tag(v_x_551_) == 2)
{
lean_object* v_info_569_; lean_object* v_val_570_; lean_object* v_info_571_; lean_object* v_val_572_; uint8_t v___x_573_; 
v_info_569_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_info_569_);
v_val_570_ = lean_ctor_get(v_x_550_, 1);
lean_inc_ref(v_val_570_);
lean_dec_ref_known(v_x_550_, 2);
v_info_571_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_info_571_);
v_val_572_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_val_572_);
lean_dec_ref_known(v_x_551_, 2);
v___x_573_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_569_, v_info_571_);
if (v___x_573_ == 0)
{
lean_dec_ref(v_val_572_);
lean_dec_ref(v_val_570_);
return v___x_573_;
}
else
{
uint8_t v___x_574_; 
v___x_574_ = lean_string_dec_eq(v_val_570_, v_val_572_);
lean_dec_ref(v_val_572_);
lean_dec_ref(v_val_570_);
return v___x_574_;
}
}
else
{
uint8_t v___x_575_; 
lean_dec_ref_known(v_x_550_, 2);
lean_dec(v_x_551_);
v___x_575_ = 0;
return v___x_575_;
}
}
default: 
{
if (lean_obj_tag(v_x_551_) == 3)
{
lean_object* v_info_576_; lean_object* v_rawVal_577_; lean_object* v_val_578_; lean_object* v_preresolved_579_; lean_object* v_info_580_; lean_object* v_rawVal_581_; lean_object* v_val_582_; lean_object* v_preresolved_583_; uint8_t v___y_585_; uint8_t v___x_588_; 
v_info_576_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_info_576_);
v_rawVal_577_ = lean_ctor_get(v_x_550_, 1);
lean_inc_ref(v_rawVal_577_);
v_val_578_ = lean_ctor_get(v_x_550_, 2);
lean_inc(v_val_578_);
v_preresolved_579_ = lean_ctor_get(v_x_550_, 3);
lean_inc(v_preresolved_579_);
lean_dec_ref_known(v_x_550_, 4);
v_info_580_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_info_580_);
v_rawVal_581_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_rawVal_581_);
v_val_582_ = lean_ctor_get(v_x_551_, 2);
lean_inc(v_val_582_);
v_preresolved_583_ = lean_ctor_get(v_x_551_, 3);
lean_inc(v_preresolved_583_);
lean_dec_ref_known(v_x_551_, 4);
v___x_588_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_576_, v_info_580_);
if (v___x_588_ == 0)
{
lean_dec_ref(v_rawVal_581_);
lean_dec_ref(v_rawVal_577_);
v___y_585_ = v___x_588_;
goto v___jp_584_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = l_Substring_Raw_beq(v_rawVal_577_, v_rawVal_581_);
v___y_585_ = v___x_589_;
goto v___jp_584_;
}
v___jp_584_:
{
if (v___y_585_ == 0)
{
lean_dec(v_preresolved_583_);
lean_dec(v_val_582_);
lean_dec(v_preresolved_579_);
lean_dec(v_val_578_);
return v___y_585_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = lean_name_eq(v_val_578_, v_val_582_);
lean_dec(v_val_582_);
lean_dec(v_val_578_);
if (v___x_586_ == 0)
{
lean_dec(v_preresolved_583_);
lean_dec(v_preresolved_579_);
return v___x_586_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_579_, v_preresolved_583_);
lean_dec(v_preresolved_583_);
lean_dec(v_preresolved_579_);
return v___x_587_;
}
}
}
}
else
{
uint8_t v___x_590_; 
lean_dec_ref_known(v_x_550_, 4);
lean_dec(v_x_551_);
v___x_590_ = 0;
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_591_, lean_object* v_ys_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_zero_594_; uint8_t v_isZero_595_; 
v_zero_594_ = lean_unsigned_to_nat(0u);
v_isZero_595_ = lean_nat_dec_eq(v_x_593_, v_zero_594_);
if (v_isZero_595_ == 1)
{
lean_dec(v_x_593_);
return v_isZero_595_;
}
else
{
lean_object* v_one_596_; lean_object* v_n_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_one_596_ = lean_unsigned_to_nat(1u);
v_n_597_ = lean_nat_sub(v_x_593_, v_one_596_);
lean_dec(v_x_593_);
v___x_598_ = lean_array_fget_borrowed(v_xs_591_, v_n_597_);
v___x_599_ = lean_array_fget_borrowed(v_ys_592_, v_n_597_);
lean_inc(v___x_599_);
lean_inc(v___x_598_);
v___x_600_ = l_Lean_Syntax_eqWithInfo(v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
lean_dec(v_n_597_);
return v___x_600_;
}
else
{
v_x_593_ = v_n_597_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_602_, lean_object* v_ys_603_, lean_object* v_x_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_602_, v_ys_603_, v_x_604_);
lean_dec_ref(v_ys_603_);
lean_dec_ref(v_xs_602_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l_Lean_Syntax_eqWithInfo(v_x_607_, v_x_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_611_, lean_object* v_ys_612_, lean_object* v_hsz_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_611_, v_ys_612_, v_x_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_617_, lean_object* v_ys_618_, lean_object* v_hsz_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_617_, v_ys_618_, v_hsz_619_, v_x_620_, v_x_621_);
lean_dec_ref(v_ys_618_);
lean_dec_ref(v_xs_617_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_624_, lean_object* v_stx1_625_, lean_object* v_stx2_626_){
_start:
{
uint8_t v___x_627_; uint8_t v___x_628_; 
lean_inc(v_stx2_626_);
lean_inc(v_stx1_625_);
v___x_627_ = l_Lean_Syntax_eqWithInfo(v_stx1_625_, v_stx2_626_);
v___x_628_ = 1;
if (v___x_627_ == 0)
{
lean_object* v_map_629_; lean_object* v___x_630_; lean_object* v___f_631_; uint8_t v___y_633_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_map_629_ = lean_ctor_get(v_opts_624_, 0);
v___x_630_ = lean_box(v___x_627_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_631_, 0, v___x_630_);
v___x_648_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_629_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
v___y_633_ = v___x_627_;
goto v___jp_632_;
}
else
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
if (lean_obj_tag(v_val_650_) == 1)
{
uint8_t v_v_651_; 
v_v_651_ = lean_ctor_get_uint8(v_val_650_, 0);
lean_dec_ref_known(v_val_650_, 0);
v___y_633_ = v_v_651_;
goto v___jp_632_;
}
else
{
lean_dec(v_val_650_);
v___y_633_ = v___x_627_;
goto v___jp_632_;
}
}
v___jp_632_:
{
if (v___y_633_ == 0)
{
lean_dec_ref(v___f_631_);
lean_dec(v_stx2_626_);
lean_dec(v_stx1_625_);
return v___x_627_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_634_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_Syntax_formatStx(v_stx1_625_, v___x_635_, v___x_628_);
v___x_637_ = l_Std_Format_defWidth;
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Std_Format_pretty(v___x_636_, v___x_637_, v___x_638_, v___x_638_);
v___x_640_ = lean_string_append(v___x_634_, v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = l_Lean_Syntax_formatStx(v_stx2_626_, v___x_635_, v___x_628_);
v___x_644_ = l_Std_Format_pretty(v___x_643_, v___x_637_, v___x_638_, v___x_638_);
v___x_645_ = lean_string_append(v___x_642_, v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = lean_dbg_trace(v___x_645_, v___f_631_);
v___x_647_ = lean_unbox(v___x_646_);
lean_dec(v___x_646_);
return v___x_647_;
}
}
}
else
{
lean_dec(v_stx2_626_);
lean_dec(v_stx1_625_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_652_, lean_object* v_stx1_653_, lean_object* v_stx2_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_652_, v_stx1_653_, v_stx2_654_);
lean_dec_ref(v_opts_652_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 2)
{
lean_object* v_val_659_; 
v_val_659_ = lean_ctor_get(v_x_658_, 1);
lean_inc_ref(v_val_659_);
return v_val_659_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Syntax_getAtomVal(v_x_661_);
lean_dec(v_x_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_663_) == 2)
{
lean_object* v_info_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_info_665_ = lean_ctor_get(v_x_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_x_663_, 1);
lean_dec(v_unused_673_);
v___x_667_ = v_x_663_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_info_665_);
lean_dec(v_x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v_x_664_);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_info_665_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_x_664_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_dec_ref(v_x_664_);
return v_x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_674_, lean_object* v_hyes_675_, lean_object* v_hno_676_){
_start:
{
if (lean_obj_tag(v_stx_674_) == 1)
{
lean_object* v___x_677_; 
lean_dec(v_hno_676_);
v___x_677_ = lean_apply_1(v_hyes_675_, v_stx_674_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v_hyes_675_);
lean_dec(v_stx_674_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_apply_1(v_hno_676_, v___x_678_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_680_, lean_object* v_stx_681_, lean_object* v_hyes_682_, lean_object* v_hno_683_){
_start:
{
if (lean_obj_tag(v_stx_681_) == 1)
{
lean_object* v___x_684_; 
lean_dec(v_hno_683_);
v___x_684_ = lean_apply_1(v_hyes_682_, v_stx_681_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_hyes_682_);
lean_dec(v_stx_681_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_apply_1(v_hno_683_, v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_687_, lean_object* v_kind_688_, lean_object* v_hyes_689_, lean_object* v_hno_690_){
_start:
{
if (lean_obj_tag(v_stx_687_) == 1)
{
lean_object* v_kind_691_; uint8_t v___x_692_; 
v_kind_691_ = lean_ctor_get(v_stx_687_, 1);
v___x_692_ = lean_name_eq(v_kind_691_, v_kind_688_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref_known(v_stx_687_, 3);
lean_dec(v_hyes_689_);
v___x_693_ = lean_box(0);
v___x_694_ = lean_apply_1(v_hno_690_, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; 
lean_dec(v_hno_690_);
v___x_695_ = lean_apply_1(v_hyes_689_, v_stx_687_);
return v___x_695_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_hyes_689_);
lean_dec(v_stx_687_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_apply_1(v_hno_690_, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_698_, lean_object* v_kind_699_, lean_object* v_hyes_700_, lean_object* v_hno_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_698_, v_kind_699_, v_hyes_700_, v_hno_701_);
lean_dec(v_kind_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_703_, lean_object* v_stx_704_, lean_object* v_kind_705_, lean_object* v_hyes_706_, lean_object* v_hno_707_){
_start:
{
if (lean_obj_tag(v_stx_704_) == 1)
{
lean_object* v_kind_708_; uint8_t v___x_709_; 
v_kind_708_ = lean_ctor_get(v_stx_704_, 1);
v___x_709_ = lean_name_eq(v_kind_708_, v_kind_705_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref_known(v_stx_704_, 3);
lean_dec(v_hyes_706_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_apply_1(v_hno_707_, v___x_710_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; 
lean_dec(v_hno_707_);
v___x_712_ = lean_apply_1(v_hyes_706_, v_stx_704_);
return v___x_712_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_hyes_706_);
lean_dec(v_stx_704_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_apply_1(v_hno_707_, v___x_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_715_, lean_object* v_stx_716_, lean_object* v_kind_717_, lean_object* v_hyes_718_, lean_object* v_hno_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_715_, v_stx_716_, v_kind_717_, v_hyes_718_, v_hno_719_);
lean_dec(v_kind_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 1)
{
lean_inc_ref(v_x_730_);
return v_x_730_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Syntax_asNode(v_x_732_);
lean_dec(v_x_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_734_, lean_object* v_i_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = l_Lean_Syntax_getArg(v_stx_734_, v_i_735_);
v___x_737_ = l_Lean_Syntax_getId(v___x_736_);
lean_dec(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_738_, lean_object* v_i_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Syntax_getIdAt(v_stx_738_, v_i_739_);
lean_dec(v_i_739_);
lean_dec(v_stx_738_);
return v_res_740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_741_, lean_object* v_x_742_){
_start:
{
switch(lean_obj_tag(v_x_742_))
{
case 3:
{
lean_object* v_val_743_; uint8_t v___x_744_; 
v_val_743_ = lean_ctor_get(v_x_742_, 2);
v___x_744_ = lean_name_eq(v_id_741_, v_val_743_);
return v___x_744_;
}
case 1:
{
lean_object* v_args_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_args_745_ = lean_ctor_get(v_x_742_, 2);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_array_get_size(v_args_745_);
v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
return v___x_748_;
}
else
{
if (v___x_748_ == 0)
{
return v___x_748_;
}
else
{
size_t v___x_749_; size_t v___x_750_; uint8_t v___x_751_; 
v___x_749_ = ((size_t)0ULL);
v___x_750_ = lean_usize_of_nat(v___x_747_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_741_, v_args_745_, v___x_749_, v___x_750_);
return v___x_751_;
}
}
}
default: 
{
uint8_t v___x_752_; 
v___x_752_ = 0;
return v___x_752_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_753_, lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
v___x_759_ = l_Lean_Syntax_hasIdent(v_id_753_, v___x_758_);
if (v___x_759_ == 0)
{
size_t v___x_760_; size_t v___x_761_; 
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_add(v_i_755_, v___x_760_);
v_i_755_ = v___x_761_;
goto _start;
}
else
{
return v___x_759_;
}
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_764_, lean_object* v_as_765_, lean_object* v_i_766_, lean_object* v_stop_767_){
_start:
{
size_t v_i_boxed_768_; size_t v_stop_boxed_769_; uint8_t v_res_770_; lean_object* v_r_771_; 
v_i_boxed_768_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_stop_boxed_769_ = lean_unbox_usize(v_stop_767_);
lean_dec(v_stop_767_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_764_, v_as_765_, v_i_boxed_768_, v_stop_boxed_769_);
lean_dec_ref(v_as_765_);
lean_dec(v_id_764_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_772_, lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Lean_Syntax_hasIdent(v_id_772_, v_x_773_);
lean_dec(v_x_773_);
lean_dec(v_id_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_776_, lean_object* v_fn_777_){
_start:
{
if (lean_obj_tag(v_stx_776_) == 1)
{
lean_object* v_info_778_; lean_object* v_kind_779_; lean_object* v_args_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_info_778_ = lean_ctor_get(v_stx_776_, 0);
v_kind_779_ = lean_ctor_get(v_stx_776_, 1);
v_args_780_ = lean_ctor_get(v_stx_776_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v_stx_776_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v_stx_776_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_args_780_);
lean_inc(v_kind_779_);
lean_inc(v_info_778_);
lean_dec(v_stx_776_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_apply_1(v_fn_777_, v_args_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 2, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_info_778_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_kind_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_dec_ref(v_fn_777_);
return v_stx_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_789_, lean_object* v_i_790_, lean_object* v_fn_791_){
_start:
{
if (lean_obj_tag(v_stx_789_) == 1)
{
lean_object* v_info_792_; lean_object* v_kind_793_; lean_object* v_args_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_info_792_ = lean_ctor_get(v_stx_789_, 0);
v_kind_793_ = lean_ctor_get(v_stx_789_, 1);
v_args_794_ = lean_ctor_get(v_stx_789_, 2);
v___x_795_ = lean_array_get_size(v_args_794_);
v___x_796_ = lean_nat_dec_lt(v_i_790_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_fn_791_);
return v_stx_789_;
}
else
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_808_; 
lean_inc_ref(v_args_794_);
lean_inc(v_kind_793_);
lean_inc(v_info_792_);
v_isSharedCheck_808_ = !lean_is_exclusive(v_stx_789_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_809_ = lean_ctor_get(v_stx_789_, 2);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_stx_789_, 1);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_stx_789_, 0);
lean_dec(v_unused_811_);
v___x_798_ = v_stx_789_;
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
else
{
lean_dec(v_stx_789_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_v_800_; lean_object* v___x_801_; lean_object* v_xs_x27_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v_v_800_ = lean_array_fget(v_args_794_, v_i_790_);
v___x_801_ = lean_box(0);
v_xs_x27_802_ = lean_array_fset(v_args_794_, v_i_790_, v___x_801_);
v___x_803_ = lean_apply_1(v_fn_791_, v_v_800_);
v___x_804_ = lean_array_fset(v_xs_x27_802_, v_i_790_, v___x_803_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 2, v___x_804_);
v___x_806_ = v___x_798_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_info_792_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_kind_793_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_dec_ref(v_fn_791_);
return v_stx_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_812_, lean_object* v_i_813_, lean_object* v_fn_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Syntax_modifyArg(v_stx_812_, v_i_813_, v_fn_814_);
lean_dec(v_i_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_816_, lean_object* v_kind_817_, lean_object* v_toPure_818_, lean_object* v_____do__lift_819_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_820_, 0, v_info_816_);
lean_ctor_set(v___x_820_, 1, v_kind_817_);
lean_ctor_set(v___x_820_, 2, v_____do__lift_819_);
v___x_821_ = lean_apply_2(v_toPure_818_, lean_box(0), v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_822_, lean_object* v_x_823_, lean_object* v_o_824_){
_start:
{
if (lean_obj_tag(v_o_824_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_apply_2(v_toPure_822_, lean_box(0), v_x_823_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; 
lean_dec(v_x_823_);
v_val_826_ = lean_ctor_get(v_o_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_o_824_, 1);
v___x_827_ = lean_apply_2(v_toPure_822_, lean_box(0), v_val_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_828_, lean_object* v_fn_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 1)
{
lean_object* v_toApplicative_831_; lean_object* v_toBind_832_; lean_object* v_toPure_833_; lean_object* v_info_834_; lean_object* v_kind_835_; lean_object* v_args_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_toApplicative_831_ = lean_ctor_get(v_inst_828_, 0);
v_toBind_832_ = lean_ctor_get(v_inst_828_, 1);
lean_inc_n(v_toBind_832_, 2);
v_toPure_833_ = lean_ctor_get(v_toApplicative_831_, 1);
lean_inc_n(v_toPure_833_, 2);
v_info_834_ = lean_ctor_get(v_x_830_, 0);
v_kind_835_ = lean_ctor_get(v_x_830_, 1);
v_args_836_ = lean_ctor_get(v_x_830_, 2);
lean_inc(v_kind_835_);
lean_inc(v_info_834_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_837_, 0, v_info_834_);
lean_closure_set(v___f_837_, 1, v_kind_835_);
lean_closure_set(v___f_837_, 2, v_toPure_833_);
lean_inc_ref(v_args_836_);
lean_inc(v_fn_829_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_838_, 0, v_inst_828_);
lean_closure_set(v___f_838_, 1, v_fn_829_);
lean_closure_set(v___f_838_, 2, v_args_836_);
lean_closure_set(v___f_838_, 3, v_toBind_832_);
lean_closure_set(v___f_838_, 4, v___f_837_);
lean_closure_set(v___f_838_, 5, v_toPure_833_);
v___x_839_ = lean_apply_1(v_fn_829_, v_x_830_);
v___x_840_ = lean_apply_4(v_toBind_832_, lean_box(0), lean_box(0), v___x_839_, v___f_838_);
return v___x_840_;
}
else
{
lean_object* v_toApplicative_841_; lean_object* v_toBind_842_; lean_object* v_toPure_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_toApplicative_841_ = lean_ctor_get(v_inst_828_, 0);
lean_inc_ref(v_toApplicative_841_);
v_toBind_842_ = lean_ctor_get(v_inst_828_, 1);
lean_inc(v_toBind_842_);
lean_dec_ref(v_inst_828_);
v_toPure_843_ = lean_ctor_get(v_toApplicative_841_, 1);
lean_inc(v_toPure_843_);
lean_dec_ref(v_toApplicative_841_);
lean_inc(v_x_830_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_844_, 0, v_toPure_843_);
lean_closure_set(v___f_844_, 1, v_x_830_);
v___x_845_ = lean_apply_1(v_fn_829_, v_x_830_);
v___x_846_ = lean_apply_4(v_toBind_842_, lean_box(0), lean_box(0), v___x_845_, v___f_844_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_847_, lean_object* v_fn_848_, lean_object* v_args_849_, lean_object* v_toBind_850_, lean_object* v___f_851_, lean_object* v_toPure_852_, lean_object* v_____do__lift_853_){
_start:
{
if (lean_obj_tag(v_____do__lift_853_) == 0)
{
lean_object* v___x_854_; size_t v_sz_855_; size_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_toPure_852_);
lean_inc_ref(v_inst_847_);
v___x_854_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_854_, 0, v_inst_847_);
lean_closure_set(v___x_854_, 1, v_fn_848_);
v_sz_855_ = lean_array_size(v_args_849_);
v___x_856_ = ((size_t)0ULL);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_847_, v___x_854_, v_sz_855_, v___x_856_, v_args_849_);
v___x_858_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v___x_857_, v___f_851_);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_860_; 
lean_dec(v___f_851_);
lean_dec(v_toBind_850_);
lean_dec_ref(v_args_849_);
lean_dec(v_fn_848_);
lean_dec_ref(v_inst_847_);
v_val_859_ = lean_ctor_get(v_____do__lift_853_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v_____do__lift_853_, 1);
v___x_860_ = lean_apply_2(v_toPure_852_, lean_box(0), v_val_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_861_, lean_object* v_inst_862_, lean_object* v_fn_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Syntax_replaceM___redArg(v_inst_862_, v_fn_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_866_, lean_object* v_kind_867_, lean_object* v_fn_868_, lean_object* v_args_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_870_, 0, v_info_866_);
lean_ctor_set(v___x_870_, 1, v_kind_867_);
lean_ctor_set(v___x_870_, 2, v_args_869_);
v___x_871_ = lean_apply_1(v_fn_868_, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_872_, lean_object* v_fn_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 1)
{
lean_object* v_toBind_875_; lean_object* v_info_876_; lean_object* v_kind_877_; lean_object* v_args_878_; lean_object* v___f_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_toBind_875_ = lean_ctor_get(v_inst_872_, 1);
lean_inc(v_toBind_875_);
v_info_876_ = lean_ctor_get(v_x_874_, 0);
lean_inc(v_info_876_);
v_kind_877_ = lean_ctor_get(v_x_874_, 1);
lean_inc(v_kind_877_);
v_args_878_ = lean_ctor_get(v_x_874_, 2);
lean_inc_ref(v_args_878_);
lean_dec_ref_known(v_x_874_, 3);
lean_inc(v_fn_873_);
v___f_879_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_879_, 0, v_info_876_);
lean_closure_set(v___f_879_, 1, v_kind_877_);
lean_closure_set(v___f_879_, 2, v_fn_873_);
lean_inc_ref(v_inst_872_);
v___x_880_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_880_, 0, v_inst_872_);
lean_closure_set(v___x_880_, 1, v_fn_873_);
v_sz_881_ = lean_array_size(v_args_878_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_872_, v___x_880_, v_sz_881_, v___x_882_, v_args_878_);
v___x_884_ = lean_apply_4(v_toBind_875_, lean_box(0), lean_box(0), v___x_883_, v___f_879_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
lean_dec_ref(v_inst_872_);
v___x_885_ = lean_apply_1(v_fn_873_, v_x_874_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_886_, lean_object* v_inst_887_, lean_object* v_fn_888_, lean_object* v_x_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_887_, v_fn_888_, v_x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_1(v_fn_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_913_, lean_object* v_stx_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_915_, 0, v_fn_913_);
v___x_916_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_917_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_916_, v___f_915_, v_stx_914_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_leading_921_; lean_object* v_trailing_922_; lean_object* v_pos_923_; lean_object* v_endPos_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_951_; 
v_leading_921_ = lean_ctor_get(v_x_918_, 0);
v_trailing_922_ = lean_ctor_get(v_x_918_, 2);
v_pos_923_ = lean_ctor_get(v_x_918_, 1);
v_endPos_924_ = lean_ctor_get(v_x_918_, 3);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_951_ == 0)
{
v___x_926_ = v_x_918_;
v_isShared_927_ = v_isSharedCheck_951_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_endPos_924_);
lean_inc(v_trailing_922_);
lean_inc(v_pos_923_);
lean_inc(v_leading_921_);
lean_dec(v_x_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_951_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_str_928_; lean_object* v_stopPos_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_949_; 
v_str_928_ = lean_ctor_get(v_leading_921_, 0);
v_stopPos_929_ = lean_ctor_get(v_leading_921_, 2);
v_isSharedCheck_949_ = !lean_is_exclusive(v_leading_921_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_leading_921_, 1);
lean_dec(v_unused_950_);
v___x_931_ = v_leading_921_;
v_isShared_932_ = v_isSharedCheck_949_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_stopPos_929_);
lean_inc(v_str_928_);
lean_dec(v_leading_921_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_949_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_str_933_; lean_object* v_startPos_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_947_; 
v_str_933_ = lean_ctor_get(v_trailing_922_, 0);
v_startPos_934_ = lean_ctor_get(v_trailing_922_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_trailing_922_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_trailing_922_, 2);
lean_dec(v_unused_948_);
v___x_936_ = v_trailing_922_;
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_startPos_934_);
lean_inc(v_str_933_);
lean_dec(v_trailing_922_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v_stopPos_929_);
lean_ctor_set(v___x_936_, 1, v_x_919_);
lean_ctor_set(v___x_936_, 0, v_str_928_);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_str_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_x_919_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_stopPos_929_);
v___x_939_ = v_reuseFailAlloc_946_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v_x_920_);
lean_ctor_set(v___x_931_, 1, v_startPos_934_);
lean_ctor_set(v___x_931_, 0, v_str_933_);
v___x_941_ = v___x_931_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_str_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_startPos_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_x_920_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 2, v___x_941_);
lean_ctor_set(v___x_926_, 0, v___x_939_);
v___x_943_ = v___x_926_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_pos_923_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_endPos_924_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_920_);
lean_dec(v_x_919_);
return v_x_918_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_952_, lean_object* v___x_953_, lean_object* v___x_954_, lean_object* v_a_955_, lean_object* v_b_956_){
_start:
{
lean_object* v_startInclusive_957_; lean_object* v_endExclusive_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_startInclusive_957_ = lean_ctor_get(v___x_952_, 1);
v_endExclusive_958_ = lean_ctor_get(v___x_952_, 2);
v___x_959_ = lean_nat_sub(v_endExclusive_958_, v_startInclusive_957_);
v___x_960_ = lean_nat_dec_eq(v_a_955_, v___x_959_);
lean_dec(v___x_959_);
if (v___x_960_ == 0)
{
uint32_t v___x_961_; lean_object* v___x_962_; uint32_t v___x_963_; uint8_t v___x_964_; 
v___x_961_ = 10;
v___x_962_ = lean_nat_add(v___x_953_, v_a_955_);
v___x_963_ = lean_string_utf8_get_fast(v___x_954_, v___x_962_);
v___x_964_ = lean_uint32_dec_eq(v___x_963_, v___x_961_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_a_955_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_string_utf8_next_fast(v___x_954_, v___x_962_);
lean_dec(v___x_962_);
v___x_967_ = lean_nat_sub(v___x_966_, v___x_953_);
v_a_955_ = v___x_967_;
v_b_956_ = v___x_965_;
goto _start;
}
else
{
lean_object* v___x_969_; 
lean_dec(v___x_962_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v_a_955_);
return v___x_969_;
}
}
else
{
lean_dec(v_a_955_);
lean_inc(v_b_956_);
return v_b_956_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v_a_973_, lean_object* v_b_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_970_, v___x_971_, v___x_972_, v_a_973_, v_b_974_);
lean_dec(v_b_974_);
lean_dec_ref(v___x_972_);
lean_dec(v___x_971_);
lean_dec_ref(v___x_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_976_){
_start:
{
lean_object* v_str_977_; lean_object* v_startPos_978_; lean_object* v_stopPos_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_999_; 
v_str_977_ = lean_ctor_get(v_trail_976_, 0);
v_startPos_978_ = lean_ctor_get(v_trail_976_, 1);
v_stopPos_979_ = lean_ctor_get(v_trail_976_, 2);
v_isSharedCheck_999_ = !lean_is_exclusive(v_trail_976_);
if (v_isSharedCheck_999_ == 0)
{
v___x_981_ = v_trail_976_;
v_isShared_982_ = v_isSharedCheck_999_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_stopPos_979_);
lean_inc(v_startPos_978_);
lean_inc(v_str_977_);
lean_dec(v_trail_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_999_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
uint8_t v___x_986_; 
v___x_986_ = lean_string_is_valid_pos(v_str_977_, v_startPos_978_);
if (v___x_986_ == 0)
{
lean_del_object(v___x_981_);
lean_dec_ref(v_str_977_);
goto v___jp_983_;
}
else
{
uint8_t v___x_987_; 
v___x_987_ = lean_string_is_valid_pos(v_str_977_, v_stopPos_979_);
if (v___x_987_ == 0)
{
lean_del_object(v___x_981_);
lean_dec_ref(v_str_977_);
goto v___jp_983_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = lean_nat_dec_le(v_startPos_978_, v_stopPos_979_);
if (v___x_988_ == 0)
{
lean_del_object(v___x_981_);
lean_dec_ref(v_str_977_);
goto v___jp_983_;
}
else
{
lean_object* v___x_990_; 
lean_inc(v_stopPos_979_);
lean_inc(v_startPos_978_);
lean_inc_ref(v_str_977_);
if (v_isShared_982_ == 0)
{
v___x_990_ = v___x_981_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_str_977_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_startPos_978_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_stopPos_979_);
v___x_990_ = v_reuseFailAlloc_998_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v_searcher_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_searcher_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_box(0);
v___x_993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_990_, v_startPos_978_, v_str_977_, v_searcher_991_, v___x_992_);
lean_dec_ref(v_str_977_);
lean_dec_ref(v___x_990_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_nat_sub(v_stopPos_979_, v_startPos_978_);
lean_dec(v_stopPos_979_);
v___x_995_ = lean_nat_add(v_startPos_978_, v___x_994_);
lean_dec(v___x_994_);
lean_dec(v_startPos_978_);
return v___x_995_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; 
lean_dec(v_stopPos_979_);
v_val_996_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v___x_993_, 1);
v___x_997_ = lean_nat_add(v_startPos_978_, v_val_996_);
lean_dec(v_val_996_);
lean_dec(v_startPos_978_);
return v___x_997_;
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_nat_sub(v_stopPos_979_, v_startPos_978_);
lean_dec(v_stopPos_979_);
v___x_985_ = lean_nat_add(v_startPos_978_, v___x_984_);
lean_dec(v___x_984_);
lean_dec(v_startPos_978_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v___x_1002_, lean_object* v_inst_1003_, lean_object* v_R_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_, lean_object* v_c_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1000_, v___x_1001_, v___x_1002_, v_a_1005_, v_b_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_inst_1012_, lean_object* v_R_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_, lean_object* v_c_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1009_, v___x_1010_, v___x_1011_, v_inst_1012_, v_R_1013_, v_a_1014_, v_b_1015_, v_c_1016_);
lean_dec(v_b_1015_);
lean_dec_ref(v___x_1011_);
lean_dec(v___x_1010_);
lean_dec_ref(v___x_1009_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___y_1021_; 
switch(lean_obj_tag(v_x_1018_))
{
case 2:
{
lean_object* v_info_1024_; 
v_info_1024_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_info_1024_);
if (lean_obj_tag(v_info_1024_) == 0)
{
lean_object* v_val_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1037_; 
v_val_1025_ = lean_ctor_get(v_x_1018_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_1018_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_x_1018_, 0);
lean_dec(v_unused_1038_);
v___x_1027_ = v_x_1018_;
v_isShared_1028_ = v_isSharedCheck_1037_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_val_1025_);
lean_dec(v_x_1018_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1037_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_trailing_1029_; lean_object* v_trailStop_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v_trailing_1029_ = lean_ctor_get(v_info_1024_, 2);
lean_inc_ref(v_trailing_1029_);
v_trailStop_1030_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1029_);
lean_inc(v_trailStop_1030_);
v___x_1031_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1024_, v_a_1019_, v_trailStop_1030_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1031_);
v___x_1033_ = v___x_1027_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_val_1025_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v_trailStop_1030_);
return v___x_1035_;
}
}
}
else
{
lean_dec(v_info_1024_);
lean_dec_ref_known(v_x_1018_, 2);
v___y_1021_ = v_a_1019_;
goto v___jp_1020_;
}
}
case 3:
{
lean_object* v_info_1039_; 
v_info_1039_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_info_1039_);
if (lean_obj_tag(v_info_1039_) == 0)
{
lean_object* v_rawVal_1040_; lean_object* v_val_1041_; lean_object* v_preresolved_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1054_; 
v_rawVal_1040_ = lean_ctor_get(v_x_1018_, 1);
v_val_1041_ = lean_ctor_get(v_x_1018_, 2);
v_preresolved_1042_ = lean_ctor_get(v_x_1018_, 3);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1018_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v_x_1018_, 0);
lean_dec(v_unused_1055_);
v___x_1044_ = v_x_1018_;
v_isShared_1045_ = v_isSharedCheck_1054_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_preresolved_1042_);
lean_inc(v_val_1041_);
lean_inc(v_rawVal_1040_);
lean_dec(v_x_1018_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1054_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_trailing_1046_; lean_object* v_trailStop_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_trailing_1046_ = lean_ctor_get(v_info_1039_, 2);
lean_inc_ref(v_trailing_1046_);
v_trailStop_1047_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1046_);
lean_inc(v_trailStop_1047_);
v___x_1048_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1039_, v_a_1019_, v_trailStop_1047_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_rawVal_1040_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_val_1041_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_preresolved_1042_);
v___x_1050_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_trailStop_1047_);
return v___x_1052_;
}
}
}
else
{
lean_dec(v_info_1039_);
lean_dec_ref_known(v_x_1018_, 4);
v___y_1021_ = v_a_1019_;
goto v___jp_1020_;
}
}
default: 
{
lean_dec(v_x_1018_);
v___y_1021_ = v_a_1019_;
goto v___jp_1020_;
}
}
v___jp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___y_1021_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
switch(lean_obj_tag(v___y_1056_))
{
case 2:
{
lean_object* v_info_1061_; 
v_info_1061_ = lean_ctor_get(v___y_1056_, 0);
lean_inc(v_info_1061_);
if (lean_obj_tag(v_info_1061_) == 0)
{
lean_object* v_val_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1074_; 
v_val_1062_ = lean_ctor_get(v___y_1056_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___y_1056_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v___y_1056_, 0);
lean_dec(v_unused_1075_);
v___x_1064_ = v___y_1056_;
v_isShared_1065_ = v_isSharedCheck_1074_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_val_1062_);
lean_dec(v___y_1056_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1074_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_trailing_1066_; lean_object* v_trailStop_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v_trailing_1066_ = lean_ctor_get(v_info_1061_, 2);
lean_inc_ref(v_trailing_1066_);
v_trailStop_1067_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1066_);
lean_inc(v_trailStop_1067_);
v___x_1068_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1061_, v___y_1057_, v_trailStop_1067_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1068_);
v___x_1070_ = v___x_1064_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_val_1062_);
v___x_1070_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_trailStop_1067_);
return v___x_1072_;
}
}
}
else
{
lean_dec(v_info_1061_);
lean_dec_ref_known(v___y_1056_, 2);
goto v___jp_1058_;
}
}
case 3:
{
lean_object* v_info_1076_; 
v_info_1076_ = lean_ctor_get(v___y_1056_, 0);
lean_inc(v_info_1076_);
if (lean_obj_tag(v_info_1076_) == 0)
{
lean_object* v_rawVal_1077_; lean_object* v_val_1078_; lean_object* v_preresolved_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1091_; 
v_rawVal_1077_ = lean_ctor_get(v___y_1056_, 1);
v_val_1078_ = lean_ctor_get(v___y_1056_, 2);
v_preresolved_1079_ = lean_ctor_get(v___y_1056_, 3);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___y_1056_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___y_1056_, 0);
lean_dec(v_unused_1092_);
v___x_1081_ = v___y_1056_;
v_isShared_1082_ = v_isSharedCheck_1091_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_preresolved_1079_);
lean_inc(v_val_1078_);
lean_inc(v_rawVal_1077_);
lean_dec(v___y_1056_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1091_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_trailing_1083_; lean_object* v_trailStop_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v_trailing_1083_ = lean_ctor_get(v_info_1076_, 2);
lean_inc_ref(v_trailing_1083_);
v_trailStop_1084_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1083_);
lean_inc(v_trailStop_1084_);
v___x_1085_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1076_, v___y_1057_, v_trailStop_1084_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1085_);
v___x_1087_ = v___x_1081_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_rawVal_1077_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_val_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_preresolved_1079_);
v___x_1087_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_trailStop_1084_);
return v___x_1089_;
}
}
}
else
{
lean_dec_ref_known(v___y_1056_, 4);
lean_dec(v_info_1076_);
goto v___jp_1058_;
}
}
default: 
{
lean_dec(v___y_1056_);
goto v___jp_1058_;
}
}
v___jp_1058_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___y_1057_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1093_, lean_object* v___y_1094_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 1)
{
lean_object* v_info_1095_; lean_object* v_kind_1096_; lean_object* v_args_1097_; lean_object* v___x_1098_; lean_object* v_fst_1099_; 
v_info_1095_ = lean_ctor_get(v_x_1093_, 0);
lean_inc(v_info_1095_);
v_kind_1096_ = lean_ctor_get(v_x_1093_, 1);
lean_inc(v_kind_1096_);
v_args_1097_ = lean_ctor_get(v_x_1093_, 2);
lean_inc_ref(v_args_1097_);
v___x_1098_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1093_, v___y_1094_);
v_fst_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_fst_1099_);
if (lean_obj_tag(v_fst_1099_) == 0)
{
lean_object* v_snd_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_snd_1100_ = lean_ctor_get(v___x_1098_, 1);
lean_inc(v_snd_1100_);
lean_dec_ref(v___x_1098_);
v_sz_1101_ = lean_array_size(v_args_1097_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1101_, v___x_1102_, v_args_1097_, v_snd_1100_);
v_fst_1104_ = lean_ctor_get(v___x_1103_, 0);
v_snd_1105_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v___x_1103_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_snd_1105_);
lean_inc(v_fst_1104_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1109_, 0, v_info_1095_);
lean_ctor_set(v___x_1109_, 1, v_kind_1096_);
lean_ctor_set(v___x_1109_, 2, v_fst_1104_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1105_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_object* v_snd_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_args_1097_);
lean_dec(v_kind_1096_);
lean_dec(v_info_1095_);
v_snd_1114_ = lean_ctor_get(v___x_1098_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1098_, 0);
lean_dec(v_unused_1123_);
v___x_1116_ = v___x_1098_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_snd_1114_);
lean_dec(v___x_1098_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_val_1118_; lean_object* v___x_1120_; 
v_val_1118_ = lean_ctor_get(v_fst_1099_, 0);
lean_inc(v_val_1118_);
lean_dec_ref_known(v_fst_1099_, 1);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v_val_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_val_1118_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_snd_1114_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v_fst_1125_; 
lean_inc(v_x_1093_);
v___x_1124_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1093_, v___y_1094_);
v_fst_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_fst_1125_);
if (lean_obj_tag(v_fst_1125_) == 0)
{
lean_object* v_snd_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_snd_1126_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1134_);
v___x_1128_ = v___x_1124_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snd_1126_);
lean_dec(v___x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_x_1093_);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_x_1093_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_snd_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_x_1093_);
v_snd_1135_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1144_);
v___x_1137_ = v___x_1124_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_dec(v___x_1124_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_val_1139_; lean_object* v___x_1141_; 
v_val_1139_ = lean_ctor_get(v_fst_1125_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v_fst_1125_, 1);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_val_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_val_1139_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_snd_1135_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_bs_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_bs_1147_);
lean_ctor_set(v___x_1150_, 1, v___y_1148_);
return v___x_1150_;
}
else
{
lean_object* v_v_1151_; lean_object* v___x_1152_; lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1155_; lean_object* v_bs_x27_1156_; size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
v_v_1151_ = lean_array_uget_borrowed(v_bs_1147_, v_i_1146_);
lean_inc(v_v_1151_);
v___x_1152_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1151_, v___y_1148_);
v_fst_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_fst_1153_);
v_snd_1154_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_snd_1154_);
lean_dec_ref(v___x_1152_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v_bs_x27_1156_ = lean_array_uset(v_bs_1147_, v_i_1146_, v___x_1155_);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_add(v_i_1146_, v___x_1157_);
v___x_1159_ = lean_array_uset(v_bs_x27_1156_, v_i_1146_, v_fst_1153_);
v_i_1146_ = v___x_1158_;
v_bs_1147_ = v___x_1159_;
v___y_1148_ = v_snd_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1161_, lean_object* v_i_1162_, lean_object* v_bs_1163_, lean_object* v___y_1164_){
_start:
{
size_t v_sz_boxed_1165_; size_t v_i_boxed_1166_; lean_object* v_res_1167_; 
v_sz_boxed_1165_ = lean_unbox_usize(v_sz_1161_);
lean_dec(v_sz_1161_);
v_i_boxed_1166_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1165_, v_i_boxed_1166_, v_bs_1163_, v___y_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_fst_1171_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1168_, v___x_1169_);
v_fst_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_fst_1171_);
lean_dec_ref(v___x_1170_);
return v_fst_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1172_, lean_object* v_x_1173_){
_start:
{
switch(lean_obj_tag(v_x_1173_))
{
case 2:
{
lean_object* v_info_1174_; lean_object* v_val_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_info_1174_ = lean_ctor_get(v_x_1173_, 0);
v_val_1175_ = lean_ctor_get(v_x_1173_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v_x_1173_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_val_1175_);
lean_inc(v_info_1174_);
lean_dec(v_x_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1172_, v_info_1174_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_val_1175_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
case 3:
{
lean_object* v_info_1184_; lean_object* v_rawVal_1185_; lean_object* v_val_1186_; lean_object* v_preresolved_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1195_; 
v_info_1184_ = lean_ctor_get(v_x_1173_, 0);
v_rawVal_1185_ = lean_ctor_get(v_x_1173_, 1);
v_val_1186_ = lean_ctor_get(v_x_1173_, 2);
v_preresolved_1187_ = lean_ctor_get(v_x_1173_, 3);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1189_ = v_x_1173_;
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_preresolved_1187_);
lean_inc(v_val_1186_);
lean_inc(v_rawVal_1185_);
lean_inc(v_info_1184_);
lean_dec(v_x_1173_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1172_, v_info_1184_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_rawVal_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_val_1186_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_preresolved_1187_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
case 1:
{
lean_object* v_info_1196_; lean_object* v_kind_1197_; lean_object* v_args_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_info_1196_ = lean_ctor_get(v_x_1173_, 0);
v_kind_1197_ = lean_ctor_get(v_x_1173_, 1);
v_args_1198_ = lean_ctor_get(v_x_1173_, 2);
v___x_1199_ = lean_array_get_size(v_args_1198_);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_nat_dec_eq(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1213_; 
lean_inc_ref(v_args_1198_);
lean_inc(v_kind_1197_);
lean_inc(v_info_1196_);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; lean_object* v_unused_1215_; lean_object* v_unused_1216_; 
v_unused_1214_ = lean_ctor_get(v_x_1173_, 2);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_x_1173_, 1);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_x_1173_, 0);
lean_dec(v_unused_1216_);
v___x_1203_ = v_x_1173_;
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_x_1173_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v_i_1206_; lean_object* v___x_1207_; lean_object* v_last_1208_; lean_object* v_args_1209_; lean_object* v___x_1211_; 
v___x_1205_ = lean_unsigned_to_nat(1u);
v_i_1206_ = lean_nat_sub(v___x_1199_, v___x_1205_);
v___x_1207_ = lean_array_fget_borrowed(v_args_1198_, v_i_1206_);
lean_inc(v___x_1207_);
v_last_1208_ = l_Lean_Syntax_updateTrailing(v_trailing_1172_, v___x_1207_);
v_args_1209_ = lean_array_fset(v_args_1198_, v_i_1206_, v_last_1208_);
lean_dec(v_i_1206_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 2, v_args_1209_);
v___x_1211_ = v___x_1203_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_info_1196_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_kind_1197_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_args_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_dec_ref(v_trailing_1172_);
return v_x_1173_;
}
}
default: 
{
lean_dec_ref(v_trailing_1172_);
return v_x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(lean_object* v_x_1217_, lean_object* v_x_1218_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 0)
{
return v_x_1217_;
}
else
{
lean_object* v_head_1219_; lean_object* v_tail_1220_; lean_object* v___x_1221_; 
v_head_1219_ = lean_ctor_get(v_x_1218_, 0);
lean_inc(v_head_1219_);
v_tail_1220_ = lean_ctor_get(v_x_1218_, 1);
lean_inc(v_tail_1220_);
lean_dec_ref_known(v_x_1218_, 2);
v___x_1221_ = l_Lean_Name_append(v_x_1217_, v_head_1219_);
v_x_1217_ = v___x_1221_;
v_x_1218_ = v_tail_1220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1225_, lean_object* v_nFields_x3f_1226_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1226_) == 1)
{
lean_object* v_val_1227_; lean_object* v_nameComps_1228_; lean_object* v___x_1229_; lean_object* v_nPrefix_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_namePrefix_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_val_1227_ = lean_ctor_get(v_nFields_x3f_1226_, 0);
v_nameComps_1228_ = l_Lean_Name_components(v_n_1225_);
v___x_1229_ = l_List_lengthTR___redArg(v_nameComps_1228_);
v_nPrefix_1230_ = lean_nat_sub(v___x_1229_, v_val_1227_);
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v___x_1232_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0));
lean_inc(v_nPrefix_1230_);
lean_inc(v_nameComps_1228_);
v___x_1233_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1228_, v_nameComps_1228_, v_nPrefix_1230_, v___x_1232_);
v_namePrefix_1234_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(v___x_1231_, v___x_1233_);
v___x_1235_ = l_List_drop___redArg(v_nPrefix_1230_, v_nameComps_1228_);
lean_dec(v_nameComps_1228_);
v___x_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_namePrefix_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Name_components(v_n_1225_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1238_, lean_object* v_nFields_x3f_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1238_, v_nFields_x3f_1239_);
lean_dec(v_nFields_x3f_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__3(lean_object* v_msg_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_panic_fn_borrowed(v___x_1242_, v_msg_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1245_ = lean_string_utf8_byte_size(v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1246_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_rawVal_1250_, lean_object* v_pos_1251_, lean_object* v_trailing_1252_, lean_object* v_leading_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
if (lean_obj_tag(v_a_1254_) == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v_leading_1253_);
lean_dec_ref(v_trailing_1252_);
v___x_1256_ = l_List_reverse___redArg(v_a_1255_);
return v___x_1256_;
}
else
{
lean_object* v_head_1257_; lean_object* v_snd_1258_; lean_object* v_tail_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1289_; 
v_head_1257_ = lean_ctor_get(v_a_1254_, 0);
lean_inc(v_head_1257_);
v_snd_1258_ = lean_ctor_get(v_head_1257_, 1);
lean_inc(v_snd_1258_);
v_tail_1259_ = lean_ctor_get(v_a_1254_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_a_1254_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_a_1254_, 0);
lean_dec(v_unused_1290_);
v___x_1261_ = v_a_1254_;
v_isShared_1262_ = v_isSharedCheck_1289_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_tail_1259_);
lean_dec(v_a_1254_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1289_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_fst_1263_; lean_object* v_startPos_1264_; lean_object* v_stopPos_1265_; lean_object* v_startPos_1266_; lean_object* v_stopPos_1267_; lean_object* v_off_1268_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1283_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_fst_1263_ = lean_ctor_get(v_head_1257_, 0);
lean_inc(v_fst_1263_);
lean_dec(v_head_1257_);
v_startPos_1264_ = lean_ctor_get(v_snd_1258_, 1);
v_stopPos_1265_ = lean_ctor_get(v_snd_1258_, 2);
v_startPos_1266_ = lean_ctor_get(v_rawVal_1250_, 1);
v_stopPos_1267_ = lean_ctor_get(v_rawVal_1250_, 2);
v_off_1268_ = lean_nat_sub(v_startPos_1264_, v_startPos_1266_);
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_nat_dec_eq(v_off_1268_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1);
v___y_1283_ = v___x_1288_;
goto v___jp_1282_;
}
else
{
lean_inc_ref(v_leading_1253_);
v___y_1283_ = v_leading_1253_;
goto v___jp_1282_;
}
v___jp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_info_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1272_ = lean_nat_add(v_off_1268_, v_pos_1251_);
lean_dec(v_off_1268_);
v___x_1273_ = lean_nat_sub(v_stopPos_1265_, v_startPos_1264_);
v___x_1274_ = lean_nat_add(v___x_1273_, v___x_1272_);
lean_dec(v___x_1273_);
v_info_1275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1275_, 0, v___y_1270_);
lean_ctor_set(v_info_1275_, 1, v___x_1272_);
lean_ctor_set(v_info_1275_, 2, v___y_1271_);
lean_ctor_set(v_info_1275_, 3, v___x_1274_);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1277_, 0, v_info_1275_);
lean_ctor_set(v___x_1277_, 1, v_snd_1258_);
lean_ctor_set(v___x_1277_, 2, v_fst_1263_);
lean_ctor_set(v___x_1277_, 3, v___x_1276_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_a_1255_);
lean_ctor_set(v___x_1261_, 0, v___x_1277_);
v___x_1279_ = v___x_1261_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_a_1255_);
v___x_1279_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v_a_1254_ = v_tail_1259_;
v_a_1255_ = v___x_1279_;
goto _start;
}
}
v___jp_1282_:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_nat_dec_eq(v_stopPos_1265_, v_stopPos_1267_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1);
v___y_1270_ = v___y_1283_;
v___y_1271_ = v___x_1285_;
goto v___jp_1269_;
}
else
{
lean_inc_ref(v_trailing_1252_);
v___y_1270_ = v___y_1283_;
v___y_1271_ = v_trailing_1252_;
goto v___jp_1269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___boxed(lean_object* v_rawVal_1291_, lean_object* v_pos_1292_, lean_object* v_trailing_1293_, lean_object* v_leading_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(v_rawVal_1291_, v_pos_1292_, v_trailing_1293_, v_leading_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_pos_1292_);
lean_dec_ref(v_rawVal_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
return v_x_1298_;
}
else
{
lean_object* v_head_1300_; lean_object* v_tail_1301_; lean_object* v_startPos_1302_; lean_object* v_stopPos_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_head_1300_ = lean_ctor_get(v_x_1299_, 0);
v_tail_1301_ = lean_ctor_get(v_x_1299_, 1);
v_startPos_1302_ = lean_ctor_get(v_head_1300_, 1);
v_stopPos_1303_ = lean_ctor_get(v_head_1300_, 2);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_sub(v_stopPos_1303_, v_startPos_1302_);
v___x_1306_ = lean_nat_add(v_x_1298_, v___x_1305_);
lean_dec(v___x_1305_);
lean_dec(v_x_1298_);
v___x_1307_ = lean_nat_add(v___x_1306_, v___x_1304_);
lean_dec(v___x_1306_);
v_x_1298_ = v___x_1307_;
v_x_1299_ = v_tail_1301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_spec__2___boxed(lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(v_x_1309_, v_x_1310_);
lean_dec(v_x_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
if (lean_obj_tag(v_a_1313_) == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_info_1312_);
v___x_1315_ = l_List_reverse___redArg(v_a_1314_);
return v___x_1315_;
}
else
{
lean_object* v_head_1316_; lean_object* v_tail_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1332_; 
v_head_1316_ = lean_ctor_get(v_a_1313_, 0);
v_tail_1317_ = lean_ctor_get(v_a_1313_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1313_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1319_ = v_a_1313_;
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_tail_1317_);
lean_inc(v_head_1316_);
lean_dec(v_a_1313_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1321_ = 1;
lean_inc(v_head_1316_);
v___x_1322_ = l_Lean_Name_toString(v_head_1316_, v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_string_utf8_byte_size(v___x_1322_);
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1322_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
v___x_1326_ = lean_box(0);
lean_inc(v_info_1312_);
v___x_1327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1327_, 0, v_info_1312_);
lean_ctor_set(v___x_1327_, 1, v___x_1325_);
lean_ctor_set(v___x_1327_, 2, v_head_1316_);
lean_ctor_set(v___x_1327_, 3, v___x_1326_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_a_1314_);
lean_ctor_set(v___x_1319_, 0, v___x_1327_);
v___x_1329_ = v___x_1319_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_a_1314_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v_a_1313_ = v_tail_1317_;
v_a_1314_ = v___x_1329_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__5(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__4));
v___x_1342_ = lean_unsigned_to_nat(9u);
v___x_1343_ = lean_unsigned_to_nat(342u);
v___x_1344_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__3));
v___x_1345_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__2));
v___x_1346_ = l_mkPanicMessageWithDecl(v___x_1345_, v___x_1344_, v___x_1343_, v___x_1342_, v___x_1341_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1347_, lean_object* v_nFields_x3f_1348_){
_start:
{
if (lean_obj_tag(v_stx_1347_) == 3)
{
lean_object* v_info_1349_; lean_object* v_rawVal_1350_; lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1409_; 
v_info_1349_ = lean_ctor_get(v_stx_1347_, 0);
v_rawVal_1350_ = lean_ctor_get(v_stx_1347_, 1);
v_val_1351_ = lean_ctor_get(v_stx_1347_, 2);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_stx_1347_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_stx_1347_, 3);
lean_dec(v_unused_1410_);
v___x_1353_ = v_stx_1347_;
v_isShared_1354_ = v_isSharedCheck_1409_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_inc(v_rawVal_1350_);
lean_inc(v_info_1349_);
lean_dec(v_stx_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1409_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_val_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_val_1355_ = l_Lean_Name_eraseMacroScopes(v_val_1351_);
lean_dec(v_val_1351_);
v___x_1356_ = l_Lean_Name_getNumParts(v_val_1355_);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_dec_le(v___x_1356_, v___x_1357_);
lean_dec(v___x_1356_);
if (v___x_1358_ == 0)
{
lean_del_object(v___x_1353_);
if (lean_obj_tag(v_info_1349_) == 0)
{
lean_object* v_leading_1359_; lean_object* v_pos_1360_; lean_object* v_trailing_1361_; lean_object* v_nameComps_1362_; lean_object* v___y_1367_; lean_object* v_rawComps_1374_; uint8_t v___x_1375_; uint8_t v___x_1376_; 
v_leading_1359_ = lean_ctor_get(v_info_1349_, 0);
v_pos_1360_ = lean_ctor_get(v_info_1349_, 1);
v_trailing_1361_ = lean_ctor_get(v_info_1349_, 2);
v_nameComps_1362_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1355_, v_nFields_x3f_1348_);
lean_inc_ref(v_rawVal_1350_);
v_rawComps_1374_ = l_Lean_Syntax_splitNameLit(v_rawVal_1350_);
v___x_1375_ = l_List_isEmpty___redArg(v_rawComps_1374_);
v___x_1376_ = lean_bool_not(v___x_1375_);
if (v___x_1376_ == 0)
{
lean_dec(v_rawComps_1374_);
lean_dec_ref(v_rawVal_1350_);
goto v___jp_1363_;
}
else
{
if (lean_obj_tag(v_nFields_x3f_1348_) == 1)
{
lean_object* v_val_1377_; lean_object* v_str_1378_; lean_object* v_startPos_1379_; lean_object* v_stopPos_1380_; lean_object* v___x_1381_; lean_object* v_nPrefix_1382_; lean_object* v___y_1384_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_prefixSz_1390_; lean_object* v_prefixSz_1391_; lean_object* v___y_1393_; uint8_t v___x_1398_; 
v_val_1377_ = lean_ctor_get(v_nFields_x3f_1348_, 0);
v_str_1378_ = lean_ctor_get(v_rawVal_1350_, 0);
v_startPos_1379_ = lean_ctor_get(v_rawVal_1350_, 1);
v_stopPos_1380_ = lean_ctor_get(v_rawVal_1350_, 2);
v___x_1381_ = l_List_lengthTR___redArg(v_rawComps_1374_);
v_nPrefix_1382_ = lean_nat_sub(v___x_1381_, v_val_1377_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
lean_inc(v_nPrefix_1382_);
lean_inc(v_rawComps_1374_);
v___x_1389_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1374_, v_rawComps_1374_, v_nPrefix_1382_, v___x_1388_);
v_prefixSz_1390_ = l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(v___x_1387_, v___x_1389_);
lean_dec(v___x_1389_);
v_prefixSz_1391_ = lean_nat_sub(v_prefixSz_1390_, v___x_1357_);
lean_dec(v_prefixSz_1390_);
v___x_1398_ = lean_nat_dec_le(v_prefixSz_1391_, v___x_1387_);
if (v___x_1398_ == 0)
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_le(v_stopPos_1380_, v_startPos_1379_);
if (v___x_1399_ == 0)
{
lean_inc(v_startPos_1379_);
v___y_1393_ = v_startPos_1379_;
goto v___jp_1392_;
}
else
{
lean_inc(v_stopPos_1380_);
v___y_1393_ = v_stopPos_1380_;
goto v___jp_1392_;
}
}
else
{
lean_object* v___x_1400_; 
lean_dec(v_prefixSz_1391_);
v___x_1400_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__1));
v___y_1384_ = v___x_1400_;
goto v___jp_1383_;
}
v___jp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = l_List_drop___redArg(v_nPrefix_1382_, v_rawComps_1374_);
lean_dec(v_rawComps_1374_);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___y_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___y_1367_ = v___x_1386_;
goto v___jp_1366_;
}
v___jp_1392_:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_nat_add(v_startPos_1379_, v_prefixSz_1391_);
lean_dec(v_prefixSz_1391_);
v___x_1395_ = lean_nat_dec_le(v_stopPos_1380_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_inc_ref(v_str_1378_);
v___x_1396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1396_, 0, v_str_1378_);
lean_ctor_set(v___x_1396_, 1, v___y_1393_);
lean_ctor_set(v___x_1396_, 2, v___x_1394_);
v___y_1384_ = v___x_1396_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1397_; 
lean_dec(v___x_1394_);
lean_inc(v_stopPos_1380_);
lean_inc_ref(v_str_1378_);
v___x_1397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1397_, 0, v_str_1378_);
lean_ctor_set(v___x_1397_, 1, v___y_1393_);
lean_ctor_set(v___x_1397_, 2, v_stopPos_1380_);
v___y_1384_ = v___x_1397_;
goto v___jp_1383_;
}
}
}
else
{
v___y_1367_ = v_rawComps_1374_;
goto v___jp_1366_;
}
}
v___jp_1363_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1349_, v_nameComps_1362_, v___x_1364_);
return v___x_1365_;
}
v___jp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = l_List_lengthTR___redArg(v_nameComps_1362_);
v___x_1369_ = l_List_lengthTR___redArg(v___y_1367_);
v___x_1370_ = lean_nat_dec_eq(v___x_1368_, v___x_1369_);
lean_dec(v___x_1369_);
lean_dec(v___x_1368_);
if (v___x_1370_ == 0)
{
lean_dec(v___y_1367_);
lean_dec_ref(v_rawVal_1350_);
goto v___jp_1363_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_inc_ref(v_trailing_1361_);
lean_inc(v_pos_1360_);
lean_inc_ref(v_leading_1359_);
lean_dec_ref_known(v_info_1349_, 4);
v___x_1371_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1362_, v___y_1367_);
v___x_1372_ = lean_box(0);
v___x_1373_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(v_rawVal_1350_, v_pos_1360_, v_trailing_1361_, v_leading_1359_, v___x_1371_, v___x_1372_);
lean_dec(v_pos_1360_);
lean_dec_ref(v_rawVal_1350_);
return v___x_1373_;
}
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec_ref(v_rawVal_1350_);
v___x_1401_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1355_, v_nFields_x3f_1348_);
v___x_1402_ = lean_box(0);
v___x_1403_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1349_, v___x_1401_, v___x_1402_);
return v___x_1403_;
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_box(0);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v___x_1404_);
lean_ctor_set(v___x_1353_, 2, v_val_1355_);
v___x_1406_ = v___x_1353_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_info_1349_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_rawVal_1350_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_val_1355_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___x_1404_);
return v___x_1407_;
}
}
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec(v_stx_1347_);
v___x_1411_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__5, &l_Lean_Syntax_identComponents___closed__5_once, _init_l_Lean_Syntax_identComponents___closed__5);
v___x_1412_ = l_panic___at___00Lean_Syntax_identComponents_spec__3(v___x_1411_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1413_, lean_object* v_nFields_x3f_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Syntax_identComponents(v_stx_1413_, v_nFields_x3f_1414_);
lean_dec(v_nFields_x3f_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1416_, uint8_t v_firstChoiceOnly_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1418_, 0, v_stx_1416_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*1, v_firstChoiceOnly_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1419_, lean_object* v_firstChoiceOnly_1420_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1421_; lean_object* v_res_1422_; 
v_firstChoiceOnly_boxed_1421_ = lean_unbox(v_firstChoiceOnly_1420_);
v_res_1422_ = l_Lean_Syntax_topDown(v_stx_1419_, v_firstChoiceOnly_boxed_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1423_, lean_object* v_____r_1424_, lean_object* v_b_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_b_1425_);
v___x_1427_ = lean_apply_2(v_toPure_1423_, lean_box(0), v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1428_, lean_object* v_toPure_1429_, lean_object* v_____s_1430_){
_start:
{
lean_object* v_fst_1431_; 
v_fst_1431_ = lean_ctor_get(v_____s_1430_, 0);
if (lean_obj_tag(v_fst_1431_) == 0)
{
lean_object* v_snd_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_toPure_1429_);
v_snd_1432_ = lean_ctor_get(v_____s_1430_, 1);
lean_inc(v_snd_1432_);
lean_dec_ref(v_____s_1430_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_apply_2(v___f_1428_, v___x_1433_, v_snd_1432_);
return v___x_1434_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1436_; 
lean_inc_ref(v_fst_1431_);
lean_dec_ref(v_____s_1430_);
lean_dec(v___f_1428_);
v_val_1435_ = lean_ctor_get(v_fst_1431_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v_fst_1431_, 1);
v___x_1436_ = lean_apply_2(v_toPure_1429_, lean_box(0), v_val_1435_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1437_, lean_object* v_toPure_1438_, lean_object* v___x_1439_, lean_object* v_____do__lift_1440_){
_start:
{
if (lean_obj_tag(v_____do__lift_1440_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_dec(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_____do__lift_1440_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_snd_1437_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
v___x_1444_ = lean_apply_2(v_toPure_1438_, lean_box(0), v___x_1443_);
return v___x_1444_;
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_snd_1437_);
v_a_1445_ = lean_ctor_get(v_____do__lift_1440_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_____do__lift_1440_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1447_ = v_____do__lift_1440_;
v_isShared_1448_ = v_isSharedCheck_1454_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v_____do__lift_1440_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1454_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1439_);
lean_ctor_set(v___x_1449_, 1, v_a_1445_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_apply_2(v_toPure_1438_, lean_box(0), v___x_1451_);
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1455_, lean_object* v___x_1456_, lean_object* v_inst_1457_, lean_object* v_f_1458_, lean_object* v_firstChoiceOnly_1459_, lean_object* v_toBind_1460_, lean_object* v_a_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1464_; lean_object* v_res_1465_; 
v_firstChoiceOnly_boxed_1464_ = lean_unbox(v_firstChoiceOnly_1459_);
v_res_1465_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1455_, v___x_1456_, v_inst_1457_, v_f_1458_, v_firstChoiceOnly_boxed_1464_, v_toBind_1460_, v_a_1461_, v_x_1462_, v___y_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1469_, lean_object* v_stx_1470_, lean_object* v_inst_1471_, lean_object* v_f_1472_, uint8_t v_firstChoiceOnly_1473_, lean_object* v_toBind_1474_, lean_object* v___f_1475_, lean_object* v___f_1476_, lean_object* v_____do__lift_1477_){
_start:
{
if (lean_obj_tag(v_____do__lift_1477_) == 0)
{
lean_object* v___x_1478_; 
lean_dec(v___f_1476_);
lean_dec(v___f_1475_);
lean_dec(v_toBind_1474_);
lean_dec(v_f_1472_);
lean_dec_ref(v_inst_1471_);
lean_dec(v_stx_1470_);
v___x_1478_ = lean_apply_2(v_toPure_1469_, lean_box(0), v_____do__lift_1477_);
return v___x_1478_;
}
else
{
if (lean_obj_tag(v_stx_1470_) == 1)
{
lean_object* v_a_1479_; lean_object* v_kind_1480_; lean_object* v_args_1481_; 
lean_dec(v___f_1476_);
v_a_1479_ = lean_ctor_get(v_____do__lift_1477_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v_____do__lift_1477_, 1);
v_kind_1480_ = lean_ctor_get(v_stx_1470_, 1);
lean_inc(v_kind_1480_);
v_args_1481_ = lean_ctor_get(v_stx_1470_, 2);
lean_inc_ref(v_args_1481_);
lean_dec_ref_known(v_stx_1470_, 3);
if (v_firstChoiceOnly_1473_ == 0)
{
lean_dec(v_kind_1480_);
goto v___jp_1482_;
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1492_ = lean_name_eq(v_kind_1480_, v___x_1491_);
lean_dec(v_kind_1480_);
if (v___x_1492_ == 0)
{
goto v___jp_1482_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v___f_1475_);
lean_dec(v_toBind_1474_);
lean_dec(v_toPure_1469_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_get(v___x_1493_, v_args_1481_, v___x_1494_);
lean_dec_ref(v_args_1481_);
v___x_1496_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1471_, v_f_1472_, v_firstChoiceOnly_1473_, v___x_1495_, v_a_1479_);
return v___x_1496_;
}
}
v___jp_1482_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; size_t v_sz_1487_; size_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_box(v_firstChoiceOnly_1473_);
lean_inc(v_toBind_1474_);
lean_inc_ref(v_inst_1471_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1485_, 0, v_toPure_1469_);
lean_closure_set(v___f_1485_, 1, v___x_1483_);
lean_closure_set(v___f_1485_, 2, v_inst_1471_);
lean_closure_set(v___f_1485_, 3, v_f_1472_);
lean_closure_set(v___f_1485_, 4, v___x_1484_);
lean_closure_set(v___f_1485_, 5, v_toBind_1474_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1483_);
lean_ctor_set(v___x_1486_, 1, v_a_1479_);
v_sz_1487_ = lean_array_size(v_args_1481_);
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v_args_1481_, v___f_1485_, v_sz_1487_, v___x_1488_, v___x_1486_);
v___x_1490_ = lean_apply_4(v_toBind_1474_, lean_box(0), lean_box(0), v___x_1489_, v___f_1475_);
return v___x_1490_;
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v___f_1475_);
lean_dec(v_toBind_1474_);
lean_dec(v_f_1472_);
lean_dec_ref(v_inst_1471_);
lean_dec(v_stx_1470_);
lean_dec(v_toPure_1469_);
v_a_1497_ = lean_ctor_get(v_____do__lift_1477_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v_____do__lift_1477_, 1);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_apply_2(v___f_1476_, v___x_1498_, v_a_1497_);
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1500_, lean_object* v_stx_1501_, lean_object* v_inst_1502_, lean_object* v_f_1503_, lean_object* v_firstChoiceOnly_1504_, lean_object* v_toBind_1505_, lean_object* v___f_1506_, lean_object* v___f_1507_, lean_object* v_____do__lift_1508_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1509_; lean_object* v_res_1510_; 
v_firstChoiceOnly_boxed_1509_ = lean_unbox(v_firstChoiceOnly_1504_);
v_res_1510_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1500_, v_stx_1501_, v_inst_1502_, v_f_1503_, v_firstChoiceOnly_boxed_1509_, v_toBind_1505_, v___f_1506_, v___f_1507_, v_____do__lift_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1511_, lean_object* v_f_1512_, uint8_t v_firstChoiceOnly_1513_, lean_object* v_stx_1514_, lean_object* v_b_1515_){
_start:
{
lean_object* v_toApplicative_1516_; lean_object* v_toBind_1517_; lean_object* v_toPure_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; 
v_toApplicative_1516_ = lean_ctor_get(v_inst_1511_, 0);
v_toBind_1517_ = lean_ctor_get(v_inst_1511_, 1);
lean_inc_n(v_toBind_1517_, 2);
v_toPure_1518_ = lean_ctor_get(v_toApplicative_1516_, 1);
lean_inc_n(v_toPure_1518_, 3);
lean_inc(v_f_1512_);
lean_inc(v_stx_1514_);
v___x_1519_ = lean_apply_2(v_f_1512_, v_stx_1514_, v_b_1515_);
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1520_, 0, v_toPure_1518_);
lean_inc_ref(v___f_1520_);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1521_, 0, v___f_1520_);
lean_closure_set(v___f_1521_, 1, v_toPure_1518_);
v___x_1522_ = lean_box(v_firstChoiceOnly_1513_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_1523_, 0, v_toPure_1518_);
lean_closure_set(v___f_1523_, 1, v_stx_1514_);
lean_closure_set(v___f_1523_, 2, v_inst_1511_);
lean_closure_set(v___f_1523_, 3, v_f_1512_);
lean_closure_set(v___f_1523_, 4, v___x_1522_);
lean_closure_set(v___f_1523_, 5, v_toBind_1517_);
lean_closure_set(v___f_1523_, 6, v___f_1521_);
lean_closure_set(v___f_1523_, 7, v___f_1520_);
v___x_1524_ = lean_apply_4(v_toBind_1517_, lean_box(0), lean_box(0), v___x_1519_, v___f_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1525_, lean_object* v___x_1526_, lean_object* v_inst_1527_, lean_object* v_f_1528_, uint8_t v_firstChoiceOnly_1529_, lean_object* v_toBind_1530_, lean_object* v_a_1531_, lean_object* v_x_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_snd_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_snd_1534_ = lean_ctor_get(v___y_1533_, 1);
lean_inc_n(v_snd_1534_, 2);
lean_dec_ref(v___y_1533_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1535_, 0, v_snd_1534_);
lean_closure_set(v___f_1535_, 1, v_toPure_1525_);
lean_closure_set(v___f_1535_, 2, v___x_1526_);
v___x_1536_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1527_, v_f_1528_, v_firstChoiceOnly_1529_, v_a_1531_, v_snd_1534_);
v___x_1537_ = lean_apply_4(v_toBind_1530_, lean_box(0), lean_box(0), v___x_1536_, v___f_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1538_, lean_object* v_f_1539_, lean_object* v_firstChoiceOnly_1540_, lean_object* v_stx_1541_, lean_object* v_b_1542_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1543_; lean_object* v_res_1544_; 
v_firstChoiceOnly_boxed_1543_ = lean_unbox(v_firstChoiceOnly_1540_);
v_res_1544_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1538_, v_f_1539_, v_firstChoiceOnly_boxed_1543_, v_stx_1541_, v_b_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1545_, lean_object* v_inst_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_f_1548_, uint8_t v_firstChoiceOnly_1549_, lean_object* v_stx_1550_, lean_object* v_b_1551_, lean_object* v_inst_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1546_, v_f_1548_, v_firstChoiceOnly_1549_, v_stx_1550_, v_b_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1554_, lean_object* v_inst_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_f_1557_, lean_object* v_firstChoiceOnly_1558_, lean_object* v_stx_1559_, lean_object* v_b_1560_, lean_object* v_inst_1561_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1562_; lean_object* v_res_1563_; 
v_firstChoiceOnly_boxed_1562_ = lean_unbox(v_firstChoiceOnly_1558_);
v_res_1563_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1554_, v_inst_1555_, v_00_u03b2_1556_, v_f_1557_, v_firstChoiceOnly_boxed_1562_, v_stx_1559_, v_b_1560_, v_inst_1561_);
lean_dec(v_inst_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1564_, lean_object* v_____do__lift_1565_){
_start:
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v_____do__lift_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v_____do__lift_1565_);
v___x_1567_ = lean_apply_2(v_toPure_1564_, lean_box(0), v_a_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1568_, lean_object* v_toBind_1569_, lean_object* v___f_1570_, lean_object* v_00_u03b2_1571_, lean_object* v_x_1572_, lean_object* v_init_1573_, lean_object* v_f_1574_){
_start:
{
uint8_t v_firstChoiceOnly_1575_; lean_object* v_stx_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_firstChoiceOnly_1575_ = lean_ctor_get_uint8(v_x_1572_, sizeof(void*)*1);
v_stx_1576_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_stx_1576_);
lean_dec_ref(v_x_1572_);
v___x_1577_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1568_, v_f_1574_, v_firstChoiceOnly_1575_, v_stx_1576_, v_init_1573_);
v___x_1578_ = lean_apply_4(v_toBind_1569_, lean_box(0), lean_box(0), v___x_1577_, v___f_1570_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1579_){
_start:
{
lean_object* v_toApplicative_1580_; lean_object* v_toBind_1581_; lean_object* v_toPure_1582_; lean_object* v___f_1583_; lean_object* v___f_1584_; 
v_toApplicative_1580_ = lean_ctor_get(v_inst_1579_, 0);
v_toBind_1581_ = lean_ctor_get(v_inst_1579_, 1);
lean_inc(v_toBind_1581_);
v_toPure_1582_ = lean_ctor_get(v_toApplicative_1580_, 1);
lean_inc(v_toPure_1582_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1583_, 0, v_toPure_1582_);
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1584_, 0, v_inst_1579_);
lean_closure_set(v___f_1584_, 1, v_toBind_1581_);
lean_closure_set(v___f_1584_, 2, v___f_1583_);
return v___f_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1585_, lean_object* v_inst_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1589_, lean_object* v_val_1590_){
_start:
{
if (lean_obj_tag(v_info_1589_) == 0)
{
lean_object* v_leading_1591_; lean_object* v_trailing_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_leading_1591_ = lean_ctor_get(v_info_1589_, 0);
lean_inc_ref(v_leading_1591_);
v_trailing_1592_ = lean_ctor_get(v_info_1589_, 2);
lean_inc_ref(v_trailing_1592_);
lean_dec_ref_known(v_info_1589_, 4);
v___x_1593_ = lean_substring_tostring(v_leading_1591_);
v___x_1594_ = lean_string_append(v___x_1593_, v_val_1590_);
v___x_1595_ = lean_substring_tostring(v_trailing_1592_);
v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
lean_dec_ref(v___x_1595_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_info_1589_);
v___x_1597_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1598_ = lean_string_append(v___x_1597_, v_val_1590_);
v___x_1599_ = lean_string_append(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1600_, lean_object* v_val_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1600_, v_val_1601_);
lean_dec_ref(v_val_1601_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1603_, lean_object* v_as_1604_, size_t v_sz_1605_, size_t v_i_1606_, lean_object* v_b_1607_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_lt(v_i_1606_, v_sz_1605_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_b_1607_);
return v___x_1609_;
}
else
{
lean_object* v_snd_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1637_; 
v_snd_1610_ = lean_ctor_get(v_b_1607_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_b_1607_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_b_1607_, 0);
lean_dec(v_unused_1638_);
v___x_1612_ = v_b_1607_;
v_isShared_1613_ = v_isSharedCheck_1637_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_snd_1610_);
lean_dec(v_b_1607_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1637_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_array_uget_borrowed(v_as_1604_, v_i_1606_);
lean_inc(v_snd_1610_);
lean_inc(v_a_1614_);
v___x_1615_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1603_, v_a_1614_, v_snd_1610_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; 
lean_del_object(v___x_1612_);
lean_dec(v_snd_1610_);
v___x_1616_ = lean_box(0);
return v___x_1616_;
}
else
{
lean_object* v_val_1617_; 
v_val_1617_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1617_);
if (lean_obj_tag(v_val_1617_) == 0)
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1627_; 
v_isSharedCheck_1627_ = !lean_is_exclusive(v_val_1617_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v_val_1617_, 0);
lean_dec(v_unused_1628_);
v___x_1619_ = v_val_1617_;
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_val_1617_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1615_);
v___x_1622_ = v___x_1612_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_snd_1610_);
v___x_1622_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1624_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 1);
lean_ctor_set(v___x_1619_, 0, v___x_1622_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1615_, 1);
lean_dec(v_snd_1610_);
v_a_1629_ = lean_ctor_get(v_val_1617_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v_val_1617_, 1);
v___x_1630_ = lean_box(0);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v_a_1629_);
lean_ctor_set(v___x_1612_, 0, v___x_1630_);
v___x_1632_ = v___x_1612_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_a_1629_);
v___x_1632_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
size_t v___x_1633_; size_t v___x_1634_; 
v___x_1633_ = ((size_t)1ULL);
v___x_1634_ = lean_usize_add(v_i_1606_, v___x_1633_);
v_i_1606_ = v___x_1634_;
v_b_1607_ = v___x_1632_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1639_, lean_object* v_a_1640_, lean_object* v_b_1641_){
_start:
{
lean_object* v_array_1642_; lean_object* v_start_1643_; lean_object* v_stop_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1663_; 
v_array_1642_ = lean_ctor_get(v_a_1640_, 0);
v_start_1643_ = lean_ctor_get(v_a_1640_, 1);
v_stop_1644_ = lean_ctor_get(v_a_1640_, 2);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1646_ = v_a_1640_;
v_isShared_1647_ = v_isSharedCheck_1663_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_stop_1644_);
lean_inc(v_start_1643_);
lean_inc(v_array_1642_);
lean_dec(v_a_1640_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1663_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_lt(v_start_1643_, v_stop_1644_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_del_object(v___x_1646_);
lean_dec(v_stop_1644_);
lean_dec(v_start_1643_);
lean_dec_ref(v_array_1642_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_b_1641_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_array_fget_borrowed(v_array_1642_, v_start_1643_);
lean_inc(v___x_1650_);
v___x_1651_ = l_Lean_Syntax_reprint(v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1652_; 
lean_del_object(v___x_1646_);
lean_dec(v_stop_1644_);
lean_dec(v_start_1643_);
lean_dec_ref(v_array_1642_);
v___x_1652_ = lean_box(0);
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; uint8_t v___x_1654_; 
v_val_1653_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1654_ = lean_string_dec_eq(v_val_1639_, v_val_1653_);
lean_dec(v_val_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_del_object(v___x_1646_);
lean_dec(v_stop_1644_);
lean_dec(v_start_1643_);
lean_dec_ref(v_array_1642_);
v___x_1655_ = lean_box(0);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_add(v_start_1643_, v___x_1657_);
lean_dec(v_start_1643_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v___x_1658_);
v___x_1660_ = v___x_1646_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_array_1642_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_stop_1644_);
v___x_1660_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
v_a_1640_ = v___x_1660_;
v_b_1641_ = v___x_1656_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1664_, lean_object* v_stx_1665_, lean_object* v_b_1666_){
_start:
{
lean_object* v_b_1668_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v_a_1683_; 
switch(lean_obj_tag(v_stx_1665_))
{
case 2:
{
lean_object* v_info_1693_; lean_object* v_val_1694_; lean_object* v___x_1695_; lean_object* v_s_1696_; 
v_info_1693_ = lean_ctor_get(v_stx_1665_, 0);
v_val_1694_ = lean_ctor_get(v_stx_1665_, 1);
lean_inc(v_info_1693_);
v___x_1695_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1693_, v_val_1694_);
v_s_1696_ = lean_string_append(v_b_1666_, v___x_1695_);
lean_dec_ref(v___x_1695_);
v_a_1683_ = v_s_1696_;
goto v___jp_1682_;
}
case 3:
{
lean_object* v_rawVal_1697_; lean_object* v_info_1698_; lean_object* v_str_1699_; lean_object* v_startPos_1700_; lean_object* v_stopPos_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v_s_1704_; 
v_rawVal_1697_ = lean_ctor_get(v_stx_1665_, 1);
v_info_1698_ = lean_ctor_get(v_stx_1665_, 0);
v_str_1699_ = lean_ctor_get(v_rawVal_1697_, 0);
v_startPos_1700_ = lean_ctor_get(v_rawVal_1697_, 1);
v_stopPos_1701_ = lean_ctor_get(v_rawVal_1697_, 2);
v___x_1702_ = lean_string_utf8_extract(v_str_1699_, v_startPos_1700_, v_stopPos_1701_);
lean_inc(v_info_1698_);
v___x_1703_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1698_, v___x_1702_);
lean_dec_ref(v___x_1702_);
v_s_1704_ = lean_string_append(v_b_1666_, v___x_1703_);
lean_dec_ref(v___x_1703_);
v_a_1683_ = v_s_1704_;
goto v___jp_1682_;
}
case 1:
{
lean_object* v_kind_1705_; lean_object* v_args_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_kind_1705_ = lean_ctor_get(v_stx_1665_, 1);
v_args_1706_ = lean_ctor_get(v_stx_1665_, 2);
v___x_1707_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1708_ = lean_name_eq(v_kind_1705_, v___x_1707_);
if (v___x_1708_ == 0)
{
v_a_1683_ = v_b_1666_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_borrowed(v___x_1709_, v_args_1706_, v___x_1710_);
lean_inc(v___x_1711_);
v___x_1712_ = l_Lean_Syntax_reprint(v___x_1711_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref_known(v_stx_1665_, 3);
lean_dec_ref(v_b_1666_);
v___x_1713_ = lean_box(0);
return v___x_1713_;
}
else
{
lean_object* v_val_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_val_1714_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_array_get_size(v_args_1706_);
lean_inc_ref(v_args_1706_);
v___x_1717_ = l_Array_toSubarray___redArg(v_args_1706_, v___x_1715_, v___x_1716_);
v___x_1718_ = lean_box(0);
v___x_1719_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1714_, v___x_1717_, v___x_1718_);
lean_dec(v_val_1714_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref_known(v_stx_1665_, 3);
lean_dec_ref(v_b_1666_);
v___x_1720_ = lean_box(0);
return v___x_1720_;
}
else
{
lean_dec_ref_known(v___x_1719_, 1);
v_a_1683_ = v_b_1666_;
goto v___jp_1682_;
}
}
}
}
default: 
{
v_a_1683_ = v_b_1666_;
goto v___jp_1682_;
}
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1668_);
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
v___jp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___y_1673_);
v_sz_1676_ = lean_array_size(v___y_1672_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1664_, v___y_1672_, v_sz_1676_, v___x_1677_, v___x_1675_);
lean_dec_ref(v___y_1672_);
if (lean_obj_tag(v___x_1678_) == 0)
{
return v___x_1674_;
}
else
{
lean_object* v_val_1679_; lean_object* v_fst_1680_; 
v_val_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_val_1679_);
lean_dec_ref_known(v___x_1678_, 1);
v_fst_1680_ = lean_ctor_get(v_val_1679_, 0);
if (lean_obj_tag(v_fst_1680_) == 0)
{
lean_object* v_snd_1681_; 
v_snd_1681_ = lean_ctor_get(v_val_1679_, 1);
lean_inc(v_snd_1681_);
lean_dec(v_val_1679_);
v_b_1668_ = v_snd_1681_;
goto v___jp_1667_;
}
else
{
lean_inc_ref(v_fst_1680_);
lean_dec(v_val_1679_);
return v_fst_1680_;
}
}
}
v___jp_1682_:
{
if (lean_obj_tag(v_stx_1665_) == 1)
{
if (v_firstChoiceOnly_1664_ == 0)
{
lean_object* v_args_1684_; 
v_args_1684_ = lean_ctor_get(v_stx_1665_, 2);
lean_inc_ref(v_args_1684_);
lean_dec_ref_known(v_stx_1665_, 3);
v___y_1672_ = v_args_1684_;
v___y_1673_ = v_a_1683_;
goto v___jp_1671_;
}
else
{
lean_object* v_kind_1685_; lean_object* v_args_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_kind_1685_ = lean_ctor_get(v_stx_1665_, 1);
lean_inc(v_kind_1685_);
v_args_1686_ = lean_ctor_get(v_stx_1665_, 2);
lean_inc_ref(v_args_1686_);
lean_dec_ref_known(v_stx_1665_, 3);
v___x_1687_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1688_ = lean_name_eq(v_kind_1685_, v___x_1687_);
lean_dec(v_kind_1685_);
if (v___x_1688_ == 0)
{
v___y_1672_ = v_args_1686_;
v___y_1673_ = v_a_1683_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_array_get(v___x_1689_, v_args_1686_, v___x_1690_);
lean_dec_ref(v_args_1686_);
v_stx_1665_ = v___x_1691_;
v_b_1666_ = v_a_1683_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1665_);
v_b_1668_ = v_a_1683_;
goto v___jp_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1721_){
_start:
{
lean_object* v_s_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; 
v_s_1722_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1723_ = 1;
v___x_1724_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1723_, v_stx_1721_, v_s_1722_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_box(0);
return v___x_1725_;
}
else
{
lean_object* v_val_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_val_1726_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v___x_1724_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_val_1726_);
lean_dec(v___x_1724_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_a_1730_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v_val_1726_, 0);
lean_inc(v_a_1730_);
lean_dec(v_val_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_a_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1735_, lean_object* v_a_1736_, lean_object* v_b_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1735_, v_a_1736_, v_b_1737_);
lean_dec_ref(v_val_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1739_, lean_object* v_as_1740_, lean_object* v_sz_1741_, lean_object* v_i_1742_, lean_object* v_b_1743_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1744_; size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v_firstChoiceOnly_boxed_1744_ = lean_unbox(v_firstChoiceOnly_1739_);
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1741_);
lean_dec(v_sz_1741_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1744_, v_as_1740_, v_sz_boxed_1745_, v_i_boxed_1746_, v_b_1743_);
lean_dec_ref(v_as_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1748_, lean_object* v_stx_1749_, lean_object* v_b_1750_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1751_; lean_object* v_res_1752_; 
v_firstChoiceOnly_boxed_1751_ = lean_unbox(v_firstChoiceOnly_1748_);
v_res_1752_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1751_, v_stx_1749_, v_b_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1753_, lean_object* v_inst_1754_, lean_object* v_R_1755_, lean_object* v_a_1756_, lean_object* v_b_1757_, lean_object* v_c_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1753_, v_a_1756_, v_b_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1760_, lean_object* v_inst_1761_, lean_object* v_R_1762_, lean_object* v_a_1763_, lean_object* v_b_1764_, lean_object* v_c_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1760_, v_inst_1761_, v_R_1762_, v_a_1763_, v_b_1764_, v_c_1765_);
lean_dec_ref(v_val_1760_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1775_, lean_object* v_stx_1776_){
_start:
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_Syntax_isMissing(v_stx_1776_);
if (v___x_1778_ == 0)
{
if (lean_obj_tag(v_stx_1776_) == 1)
{
lean_object* v_kind_1779_; lean_object* v_args_1780_; 
v_kind_1779_ = lean_ctor_get(v_stx_1776_, 1);
v_args_1780_ = lean_ctor_get(v_stx_1776_, 2);
if (v_firstChoiceOnly_1775_ == 0)
{
goto v___jp_1781_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1791_ = lean_name_eq(v_kind_1779_, v___x_1790_);
if (v___x_1791_ == 0)
{
goto v___jp_1781_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_array_get_borrowed(v___x_1792_, v_args_1780_, v___x_1793_);
v_stx_1776_ = v___x_1794_;
goto _start;
}
}
v___jp_1781_:
{
lean_object* v___x_1782_; size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; lean_object* v_fst_1786_; 
v___x_1782_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1783_ = lean_array_size(v_args_1780_);
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1775_, v_args_1780_, v_sz_1783_, v___x_1784_, v___x_1782_);
v_fst_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_fst_1786_);
if (lean_obj_tag(v_fst_1786_) == 0)
{
lean_object* v_snd_1787_; lean_object* v___x_1788_; 
v_snd_1787_ = lean_ctor_get(v___x_1785_, 1);
lean_inc(v_snd_1787_);
lean_dec_ref(v___x_1785_);
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_snd_1787_);
return v___x_1788_;
}
else
{
lean_object* v_val_1789_; 
lean_dec_ref(v___x_1785_);
v_val_1789_ = lean_ctor_get(v_fst_1786_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v_fst_1786_, 1);
return v_val_1789_;
}
}
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1796_;
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = lean_box(v___x_1778_);
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1777_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1801_, lean_object* v_as_1802_, size_t v_sz_1803_, size_t v_i_1804_, lean_object* v_b_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_usize_dec_lt(v_i_1804_, v_sz_1803_);
if (v___x_1806_ == 0)
{
return v_b_1805_;
}
else
{
lean_object* v_snd_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1825_; 
v_snd_1807_ = lean_ctor_get(v_b_1805_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_b_1805_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v_b_1805_, 0);
lean_dec(v_unused_1826_);
v___x_1809_ = v_b_1805_;
v_isShared_1810_ = v_isSharedCheck_1825_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snd_1807_);
lean_dec(v_b_1805_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1825_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_array_uget_borrowed(v_as_1802_, v_i_1804_);
v___x_1812_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1801_, v_a_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1813_);
v___x_1815_ = v___x_1809_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_snd_1807_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
lean_dec(v_snd_1807_);
v_a_1817_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1818_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v_a_1817_);
lean_ctor_set(v___x_1809_, 0, v___x_1818_);
v___x_1820_ = v___x_1809_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_a_1817_);
v___x_1820_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
size_t v___x_1821_; size_t v___x_1822_; 
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1804_, v___x_1821_);
v_i_1804_ = v___x_1822_;
v_b_1805_ = v___x_1820_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1827_, lean_object* v_as_1828_, lean_object* v_sz_1829_, lean_object* v_i_1830_, lean_object* v_b_1831_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1832_; size_t v_sz_boxed_1833_; size_t v_i_boxed_1834_; lean_object* v_res_1835_; 
v_firstChoiceOnly_boxed_1832_ = lean_unbox(v_firstChoiceOnly_1827_);
v_sz_boxed_1833_ = lean_unbox_usize(v_sz_1829_);
lean_dec(v_sz_1829_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1832_, v_as_1828_, v_sz_boxed_1833_, v_i_boxed_1834_, v_b_1831_);
lean_dec_ref(v_as_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1836_, lean_object* v_stx_1837_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1838_; lean_object* v_res_1839_; 
v_firstChoiceOnly_boxed_1838_ = lean_unbox(v_firstChoiceOnly_1836_);
v_res_1839_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1838_, v_stx_1837_);
lean_dec(v_stx_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1840_){
_start:
{
uint8_t v___x_1841_; lean_object* v___y_1843_; lean_object* v___x_1847_; lean_object* v_a_1848_; 
v___x_1841_ = 0;
v___x_1847_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1841_, v_stx_1840_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___y_1843_ = v_a_1848_;
goto v___jp_1842_;
v___jp_1842_:
{
lean_object* v_fst_1844_; 
v_fst_1844_ = lean_ctor_get(v___y_1843_, 0);
lean_inc(v_fst_1844_);
lean_dec_ref(v___y_1843_);
if (lean_obj_tag(v_fst_1844_) == 0)
{
return v___x_1841_;
}
else
{
lean_object* v_val_1845_; uint8_t v___x_1846_; 
v_val_1845_ = lean_ctor_get(v_fst_1844_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v_fst_1844_, 1);
v___x_1846_ = lean_unbox(v_val_1845_);
lean_dec(v_val_1845_);
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Lean_Syntax_hasMissing(v_stx_1849_);
lean_dec(v_stx_1849_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1852_, lean_object* v_stx_1853_, lean_object* v_b_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1852_, v_stx_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1856_, lean_object* v_stx_1857_, lean_object* v_b_1858_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1859_; lean_object* v_res_1860_; 
v_firstChoiceOnly_boxed_1859_ = lean_unbox(v_firstChoiceOnly_1856_);
v_res_1860_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1859_, v_stx_1857_, v_b_1858_);
lean_dec_ref(v_b_1858_);
lean_dec(v_stx_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1861_, uint8_t v_canonicalOnly_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Syntax_getPos_x3f(v_stx_1861_, v_canonicalOnly_1862_);
if (lean_obj_tag(v___x_1863_) == 1)
{
lean_object* v_val_1864_; lean_object* v___x_1865_; 
v_val_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1861_, v_canonicalOnly_1862_);
if (lean_obj_tag(v___x_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1874_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_val_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_val_1864_);
lean_ctor_set(v___x_1870_, 1, v_val_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v___x_1875_; 
lean_dec(v___x_1865_);
lean_dec(v_val_1864_);
v___x_1875_ = lean_box(0);
return v___x_1875_;
}
}
else
{
lean_object* v___x_1876_; 
lean_dec(v___x_1863_);
v___x_1876_ = lean_box(0);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1877_, lean_object* v_canonicalOnly_1878_){
_start:
{
uint8_t v_canonicalOnly_boxed_1879_; lean_object* v_res_1880_; 
v_canonicalOnly_boxed_1879_ = lean_unbox(v_canonicalOnly_1878_);
v_res_1880_ = l_Lean_Syntax_getRange_x3f(v_stx_1877_, v_canonicalOnly_boxed_1879_);
lean_dec(v_stx_1877_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1881_, uint8_t v_canonicalOnly_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Syntax_getPos_x3f(v_stx_1881_, v_canonicalOnly_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_box(0);
return v___x_1884_;
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1886_; 
v_val_1885_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1886_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1881_, v_canonicalOnly_1882_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; 
lean_dec(v_val_1885_);
v___x_1887_ = lean_box(0);
return v___x_1887_;
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1896_; 
v_val_1888_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_val_1888_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v_val_1885_);
lean_ctor_set(v___x_1892_, 1, v_val_1888_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1897_, lean_object* v_canonicalOnly_1898_){
_start:
{
uint8_t v_canonicalOnly_boxed_1899_; lean_object* v_res_1900_; 
v_canonicalOnly_boxed_1899_ = lean_unbox(v_canonicalOnly_1898_);
v_res_1900_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1897_, v_canonicalOnly_boxed_1899_);
lean_dec(v_stx_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1901_, uint8_t v_canonical_1902_){
_start:
{
lean_object* v_start_1903_; lean_object* v_stop_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1913_; 
v_start_1903_ = lean_ctor_get(v_range_1901_, 0);
v_stop_1904_ = lean_ctor_get(v_range_1901_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_range_1901_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1906_ = v_range_1901_;
v_isShared_1907_ = v_isSharedCheck_1913_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_stop_1904_);
lean_inc(v_start_1903_);
lean_dec(v_range_1901_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1913_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1908_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1908_, 0, v_start_1903_);
lean_ctor_set(v___x_1908_, 1, v_stop_1904_);
lean_ctor_set_uint8(v___x_1908_, sizeof(void*)*2, v_canonical_1902_);
v___x_1909_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 2);
lean_ctor_set(v___x_1906_, 1, v___x_1909_);
lean_ctor_set(v___x_1906_, 0, v___x_1908_);
v___x_1911_ = v___x_1906_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_1914_, lean_object* v_canonical_1915_){
_start:
{
uint8_t v_canonical_boxed_1916_; lean_object* v_res_1917_; 
v_canonical_boxed_1916_ = lean_unbox(v_canonical_1915_);
v_res_1917_ = l_Lean_Syntax_ofRange(v_range_1914_, v_canonical_boxed_1916_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1922_, 0, v_stx_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
lean_ctor_set(v___x_1922_, 2, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_1923_, lean_object* v_stx_1924_){
_start:
{
lean_object* v_parents_1925_; lean_object* v_idxs_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_parents_1925_ = lean_ctor_get(v_t_1923_, 1);
v_idxs_1926_ = lean_ctor_get(v_t_1923_, 2);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_t_1923_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v_t_1923_, 0);
lean_dec(v_unused_1934_);
v___x_1928_ = v_t_1923_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_idxs_1926_);
lean_inc(v_parents_1925_);
lean_dec(v_t_1923_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v_stx_1924_);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_stx_1924_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_parents_1925_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_idxs_1926_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_1935_, lean_object* v_idx_1936_){
_start:
{
lean_object* v_cur_1937_; lean_object* v_parents_1938_; lean_object* v_idxs_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1959_; 
v_cur_1937_ = lean_ctor_get(v_t_1935_, 0);
v_parents_1938_ = lean_ctor_get(v_t_1935_, 1);
v_idxs_1939_ = lean_ctor_get(v_t_1935_, 2);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_t_1935_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1941_ = v_t_1935_;
v_isShared_1942_ = v_isSharedCheck_1959_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_idxs_1939_);
lean_inc(v_parents_1938_);
lean_inc(v_cur_1937_);
lean_dec(v_t_1935_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1959_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = l_Lean_Syntax_getNumArgs(v_cur_1937_);
v___x_1944_ = lean_nat_dec_lt(v_idx_1936_, v___x_1943_);
lean_dec(v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_array_push(v_parents_1938_, v_cur_1937_);
v___x_1947_ = lean_array_push(v_idxs_1939_, v_idx_1936_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 2, v___x_1947_);
lean_ctor_set(v___x_1941_, 1, v___x_1946_);
lean_ctor_set(v___x_1941_, 0, v___x_1945_);
v___x_1949_ = v___x_1941_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1951_ = l_Lean_Syntax_getArg(v_cur_1937_, v_idx_1936_);
v___x_1952_ = lean_box(0);
v___x_1953_ = l_Lean_Syntax_setArg(v_cur_1937_, v_idx_1936_, v___x_1952_);
v___x_1954_ = lean_array_push(v_parents_1938_, v___x_1953_);
v___x_1955_ = lean_array_push(v_idxs_1939_, v_idx_1936_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 2, v___x_1955_);
lean_ctor_set(v___x_1941_, 1, v___x_1954_);
lean_ctor_set(v___x_1941_, 0, v___x_1951_);
v___x_1957_ = v___x_1941_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_1960_){
_start:
{
lean_object* v_cur_1961_; lean_object* v_parents_1962_; lean_object* v_idxs_1963_; lean_object* v___y_1965_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_cur_1961_ = lean_ctor_get(v_t_1960_, 0);
v_parents_1962_ = lean_ctor_get(v_t_1960_, 1);
v_idxs_1963_ = lean_ctor_get(v_t_1960_, 2);
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_array_get_size(v_parents_1962_);
v___x_1971_ = lean_nat_dec_lt(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
return v_t_1960_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
lean_inc_ref(v_idxs_1963_);
lean_inc_ref(v_parents_1962_);
lean_inc(v_cur_1961_);
lean_dec_ref(v_t_1960_);
v___x_1972_ = lean_array_get_size(v_idxs_1963_);
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_nat_sub(v___x_1972_, v___x_1973_);
v___x_1975_ = lean_array_get_borrowed(v___x_1969_, v_idxs_1963_, v___x_1974_);
lean_dec(v___x_1974_);
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_nat_sub(v___x_1970_, v___x_1973_);
v___x_1978_ = lean_array_get_borrowed(v___x_1976_, v_parents_1962_, v___x_1977_);
lean_dec(v___x_1977_);
v___x_1979_ = l_Lean_Syntax_getNumArgs(v___x_1978_);
v___x_1980_ = lean_nat_dec_lt(v___x_1975_, v___x_1979_);
lean_dec(v___x_1979_);
if (v___x_1980_ == 0)
{
lean_dec(v_cur_1961_);
lean_inc(v___x_1978_);
v___y_1965_ = v___x_1978_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_1981_; 
lean_inc(v___x_1978_);
v___x_1981_ = l_Lean_Syntax_setArg(v___x_1978_, v___x_1975_, v_cur_1961_);
v___y_1965_ = v___x_1981_;
goto v___jp_1964_;
}
}
v___jp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_array_pop(v_parents_1962_);
v___x_1967_ = lean_array_pop(v_idxs_1963_);
v___x_1968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1965_);
lean_ctor_set(v___x_1968_, 1, v___x_1966_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_1982_){
_start:
{
lean_object* v_parents_1983_; lean_object* v_idxs_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_parents_1983_ = lean_ctor_get(v_t_1982_, 1);
v_idxs_1984_ = lean_ctor_get(v_t_1982_, 2);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_array_get_size(v_parents_1983_);
v___x_1987_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
return v_t_1982_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_inc_ref(v_idxs_1984_);
v___x_1988_ = l_Lean_Syntax_Traverser_up(v_t_1982_);
v___x_1989_ = lean_array_get_size(v_idxs_1984_);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_sub(v___x_1989_, v___x_1990_);
v___x_1992_ = lean_array_get(v___x_1985_, v_idxs_1984_, v___x_1991_);
lean_dec(v___x_1991_);
lean_dec_ref(v_idxs_1984_);
v___x_1993_ = lean_nat_sub(v___x_1992_, v___x_1990_);
lean_dec(v___x_1992_);
v___x_1994_ = l_Lean_Syntax_Traverser_down(v___x_1988_, v___x_1993_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_1995_){
_start:
{
lean_object* v_parents_1996_; lean_object* v_idxs_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_parents_1996_ = lean_ctor_get(v_t_1995_, 1);
v_idxs_1997_ = lean_ctor_get(v_t_1995_, 2);
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = lean_array_get_size(v_parents_1996_);
v___x_2000_ = lean_nat_dec_lt(v___x_1998_, v___x_1999_);
if (v___x_2000_ == 0)
{
return v_t_1995_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_inc_ref(v_idxs_1997_);
v___x_2001_ = l_Lean_Syntax_Traverser_up(v_t_1995_);
v___x_2002_ = lean_array_get_size(v_idxs_1997_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_sub(v___x_2002_, v___x_2003_);
v___x_2005_ = lean_array_get(v___x_1998_, v_idxs_1997_, v___x_2004_);
lean_dec(v___x_2004_);
lean_dec_ref(v_idxs_1997_);
v___x_2006_ = lean_nat_add(v___x_2005_, v___x_2003_);
lean_dec(v___x_2005_);
v___x_2007_ = l_Lean_Syntax_Traverser_down(v___x_2001_, v___x_2006_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2008_){
_start:
{
lean_object* v_cur_2009_; 
v_cur_2009_ = lean_ctor_get(v_self_2008_, 0);
lean_inc(v_cur_2009_);
return v_cur_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2010_);
lean_dec_ref(v_self_2010_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2013_, lean_object* v_t_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toFunctor_2016_; lean_object* v_map_2017_; lean_object* v_get_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2013_, 0);
lean_inc_ref(v_toApplicative_2015_);
lean_dec_ref(v_inst_2013_);
v_toFunctor_2016_ = lean_ctor_get(v_toApplicative_2015_, 0);
lean_inc_ref(v_toFunctor_2016_);
lean_dec_ref(v_toApplicative_2015_);
v_map_2017_ = lean_ctor_get(v_toFunctor_2016_, 0);
lean_inc(v_map_2017_);
lean_dec_ref(v_toFunctor_2016_);
v_get_2018_ = lean_ctor_get(v_t_2014_, 0);
lean_inc(v_get_2018_);
lean_dec_ref(v_t_2014_);
v___f_2019_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2020_ = lean_apply_4(v_map_2017_, lean_box(0), lean_box(0), v___f_2019_, v_get_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2021_, lean_object* v_inst_2022_, lean_object* v_t_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2022_, v_t_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2025_, lean_object* v_s_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_box(0);
v___x_2028_ = l_Lean_Syntax_Traverser_setCur(v_s_2026_, v_stx_2025_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2030_, lean_object* v_stx_2031_){
_start:
{
lean_object* v_modifyGet_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; 
v_modifyGet_2032_ = lean_ctor_get(v_t_2030_, 2);
lean_inc(v_modifyGet_2032_);
lean_dec_ref(v_t_2030_);
v___f_2033_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2033_, 0, v_stx_2031_);
v___x_2034_ = lean_apply_2(v_modifyGet_2032_, lean_box(0), v___f_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2035_, lean_object* v_t_2036_, lean_object* v_stx_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2036_, v_stx_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2039_, lean_object* v_s_2040_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Lean_Syntax_Traverser_down(v_s_2040_, v_idx_2039_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2044_, lean_object* v_idx_2045_){
_start:
{
lean_object* v_modifyGet_2046_; lean_object* v___f_2047_; lean_object* v___x_2048_; 
v_modifyGet_2046_ = lean_ctor_get(v_t_2044_, 2);
lean_inc(v_modifyGet_2046_);
lean_dec_ref(v_t_2044_);
v___f_2047_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2047_, 0, v_idx_2045_);
v___x_2048_ = lean_apply_2(v_modifyGet_2046_, lean_box(0), v___f_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2049_, lean_object* v_t_2050_, lean_object* v_idx_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2050_, v_idx_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = l_Lean_Syntax_Traverser_up(v_s_2053_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2058_){
_start:
{
lean_object* v_modifyGet_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; 
v_modifyGet_2059_ = lean_ctor_get(v_t_2058_, 2);
lean_inc(v_modifyGet_2059_);
lean_dec_ref(v_t_2058_);
v___f_2060_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2061_ = lean_apply_2(v_modifyGet_2059_, lean_box(0), v___f_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2062_, lean_object* v_t_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2065_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = l_Lean_Syntax_Traverser_left(v_s_2065_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2070_){
_start:
{
lean_object* v_modifyGet_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; 
v_modifyGet_2071_ = lean_ctor_get(v_t_2070_, 2);
lean_inc(v_modifyGet_2071_);
lean_dec_ref(v_t_2070_);
v___f_2072_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2073_ = lean_apply_2(v_modifyGet_2071_, lean_box(0), v___f_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2074_, lean_object* v_t_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = l_Lean_Syntax_Traverser_right(v_s_2077_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2082_){
_start:
{
lean_object* v_modifyGet_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; 
v_modifyGet_2083_ = lean_ctor_get(v_t_2082_, 2);
lean_inc(v_modifyGet_2083_);
lean_dec_ref(v_t_2082_);
v___f_2084_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2085_ = lean_apply_2(v_modifyGet_2083_, lean_box(0), v___f_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2086_, lean_object* v_t_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2089_, lean_object* v_st_2090_){
_start:
{
lean_object* v_idxs_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_idxs_2091_ = lean_ctor_get(v_st_2090_, 2);
v___x_2092_ = lean_array_get_size(v_idxs_2091_);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_sub(v___x_2092_, v___x_2093_);
v___x_2095_ = lean_nat_dec_lt(v___x_2094_, v___x_2092_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v___x_2094_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = lean_apply_2(v_toPure_2089_, lean_box(0), v___x_2096_);
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_array_fget_borrowed(v_idxs_2091_, v___x_2094_);
lean_dec(v___x_2094_);
lean_inc(v___x_2098_);
v___x_2099_ = lean_apply_2(v_toPure_2089_, lean_box(0), v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2100_, lean_object* v_st_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2100_, v_st_2101_);
lean_dec_ref(v_st_2101_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2103_, lean_object* v_t_2104_){
_start:
{
lean_object* v_toApplicative_2105_; lean_object* v_toBind_2106_; lean_object* v_get_2107_; lean_object* v_toPure_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; 
v_toApplicative_2105_ = lean_ctor_get(v_inst_2103_, 0);
lean_inc_ref(v_toApplicative_2105_);
v_toBind_2106_ = lean_ctor_get(v_inst_2103_, 1);
lean_inc(v_toBind_2106_);
lean_dec_ref(v_inst_2103_);
v_get_2107_ = lean_ctor_get(v_t_2104_, 0);
lean_inc(v_get_2107_);
lean_dec_ref(v_t_2104_);
v_toPure_2108_ = lean_ctor_get(v_toApplicative_2105_, 1);
lean_inc(v_toPure_2108_);
lean_dec_ref(v_toApplicative_2105_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2109_, 0, v_toPure_2108_);
v___x_2110_ = lean_apply_4(v_toBind_2106_, lean_box(0), lean_box(0), v_get_2107_, v___f_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2111_, lean_object* v_inst_2112_, lean_object* v_t_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2112_, v_t_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2115_, lean_object* v_i_2116_){
_start:
{
lean_object* v_args_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_args_2117_ = lean_ctor_get(v_n_2115_, 2);
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_array_get_borrowed(v___x_2118_, v_args_2117_, v_i_2116_);
v___x_2120_ = l_Lean_Syntax_getId(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2121_, lean_object* v_i_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_SyntaxNode_getIdAt(v_n_2121_, v_i_2122_);
lean_dec(v_i_2122_);
lean_dec(v_n_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2126_ = lean_box(2);
v___x_2127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v_args_2124_);
return v___x_2127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 1)
{
lean_object* v_kind_2134_; 
v_kind_2134_ = lean_ctor_get(v_x_2133_, 1);
if (lean_obj_tag(v_kind_2134_) == 1)
{
lean_object* v_pre_2135_; lean_object* v_str_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_pre_2135_ = lean_ctor_get(v_kind_2134_, 0);
v_str_2136_ = lean_ctor_get(v_kind_2134_, 1);
v___x_2137_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2138_ = lean_string_dec_eq(v_str_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2140_ = lean_string_dec_eq(v_str_2136_, v___x_2139_);
if (v___x_2140_ == 0)
{
return v___x_2140_;
}
else
{
if (lean_obj_tag(v_pre_2135_) == 1)
{
lean_object* v_pre_2141_; 
v_pre_2141_ = lean_ctor_get(v_pre_2135_, 0);
if (lean_obj_tag(v_pre_2141_) == 1)
{
lean_object* v_pre_2142_; 
v_pre_2142_ = lean_ctor_get(v_pre_2141_, 0);
if (lean_obj_tag(v_pre_2142_) == 1)
{
lean_object* v_pre_2143_; 
v_pre_2143_ = lean_ctor_get(v_pre_2142_, 0);
if (lean_obj_tag(v_pre_2143_) == 0)
{
lean_object* v_str_2144_; lean_object* v_str_2145_; lean_object* v_str_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_str_2144_ = lean_ctor_get(v_pre_2135_, 1);
v_str_2145_ = lean_ctor_get(v_pre_2141_, 1);
v_str_2146_ = lean_ctor_get(v_pre_2142_, 1);
v___x_2147_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2148_ = lean_string_dec_eq(v_str_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
return v___x_2148_;
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2150_ = lean_string_dec_eq(v_str_2145_, v___x_2149_);
if (v___x_2150_ == 0)
{
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2152_ = lean_string_dec_eq(v_str_2144_, v___x_2151_);
return v___x_2152_;
}
}
}
else
{
return v___x_2138_;
}
}
else
{
return v___x_2138_;
}
}
else
{
return v___x_2138_;
}
}
else
{
return v___x_2138_;
}
}
}
else
{
return v___x_2138_;
}
}
else
{
uint8_t v___x_2153_; 
v___x_2153_ = 0;
return v___x_2153_;
}
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = 0;
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2155_){
_start:
{
uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_res_2156_ = l_Lean_Syntax_isQuot(v_x_2155_);
lean_dec(v_x_2155_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___y_2167_; uint8_t v___x_2173_; 
v___x_2164_ = l_Lean_Syntax_getNumArgs(v_stx_2163_);
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_nat_dec_eq(v___x_2164_, v___x_2165_);
lean_dec(v___x_2164_);
if (v___x_2173_ == 0)
{
v___y_2167_ = v_stx_2163_;
goto v___jp_2166_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = l_Lean_Syntax_getArg(v_stx_2163_, v___x_2174_);
lean_dec(v_stx_2163_);
v___y_2167_ = v___x_2175_;
goto v___jp_2166_;
}
v___jp_2166_:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2167_);
v___x_2169_ = l_Lean_Syntax_isOfKind(v___y_2167_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Syntax_getArg(v___y_2167_, v___x_2165_);
lean_dec(v___y_2167_);
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(3u);
v___x_2172_ = l_Lean_Syntax_getArg(v___y_2167_, v___x_2171_);
lean_dec(v___y_2167_);
return v___x_2172_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2177_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 1)
{
lean_object* v_kind_2178_; 
v_kind_2178_ = lean_ctor_get(v_x_2177_, 1);
if (lean_obj_tag(v_kind_2178_) == 1)
{
lean_object* v_str_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_str_2179_ = lean_ctor_get(v_kind_2178_, 1);
v___x_2180_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2181_ = lean_string_dec_eq(v_str_2179_, v___x_2180_);
return v___x_2181_;
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = 0;
return v___x_2182_;
}
}
else
{
uint8_t v___x_2183_; 
v___x_2183_ = 0;
return v___x_2183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2184_){
_start:
{
uint8_t v_res_2185_; lean_object* v_r_2186_; 
v_res_2185_ = l_Lean_Syntax_isAntiquot(v_x_2184_);
lean_dec(v_x_2184_);
v_r_2186_ = lean_box(v_res_2185_);
return v_r_2186_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object* v_as_2187_, size_t v_i_2188_, size_t v_stop_2189_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_usize_dec_eq(v_i_2188_, v_stop_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; uint8_t v___x_2192_; uint8_t v___x_2193_; 
v___x_2191_ = lean_array_uget_borrowed(v_as_2187_, v_i_2188_);
v___x_2192_ = l_Lean_Syntax_isAntiquot(v___x_2191_);
v___x_2193_ = lean_bool_not(v___x_2192_);
if (v___x_2193_ == 0)
{
size_t v___x_2194_; size_t v___x_2195_; 
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2188_, v___x_2194_);
v_i_2188_ = v___x_2195_;
goto _start;
}
else
{
return v___x_2193_;
}
}
else
{
uint8_t v___x_2197_; 
v___x_2197_ = 0;
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v_as_2198_, lean_object* v_i_2199_, lean_object* v_stop_2200_){
_start:
{
size_t v_i_boxed_2201_; size_t v_stop_boxed_2202_; uint8_t v_res_2203_; lean_object* v_r_2204_; 
v_i_boxed_2201_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_stop_boxed_2202_ = lean_unbox_usize(v_stop_2200_);
lean_dec(v_stop_2200_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v_as_2198_, v_i_boxed_2201_, v_stop_boxed_2202_);
lean_dec_ref(v_as_2198_);
v_r_2204_ = lean_box(v_res_2203_);
return v_r_2204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2205_){
_start:
{
uint8_t v___x_2206_; uint8_t v___y_2208_; 
v___x_2206_ = l_Lean_Syntax_isAntiquot(v_stx_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2205_);
v___x_2220_ = l_Lean_Syntax_isOfKind(v_stx_2205_, v___x_2219_);
if (v___x_2220_ == 0)
{
v___y_2208_ = v___x_2220_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = l_Lean_Syntax_getNumArgs(v_stx_2205_);
v___x_2223_ = lean_nat_dec_lt(v___x_2221_, v___x_2222_);
lean_dec(v___x_2222_);
v___y_2208_ = v___x_2223_;
goto v___jp_2207_;
}
}
else
{
lean_dec(v_stx_2205_);
return v___x_2206_;
}
v___jp_2207_:
{
if (v___y_2208_ == 0)
{
lean_dec(v_stx_2205_);
return v___y_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2209_ = l_Lean_Syntax_getArgs(v_stx_2205_);
lean_dec(v_stx_2205_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = lean_array_get_size(v___x_2209_);
v___x_2212_ = lean_nat_dec_lt(v___x_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; 
lean_dec_ref(v___x_2209_);
v___x_2213_ = lean_bool_not(v___x_2206_);
return v___x_2213_;
}
else
{
if (v___x_2212_ == 0)
{
uint8_t v___x_2214_; 
lean_dec_ref(v___x_2209_);
v___x_2214_ = lean_bool_not(v___x_2206_);
return v___x_2214_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; uint8_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_of_nat(v___x_2211_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2209_, v___x_2215_, v___x_2216_);
lean_dec_ref(v___x_2209_);
v___x_2218_ = lean_bool_not(v___x_2217_);
return v___x_2218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2224_){
_start:
{
uint8_t v_res_2225_; lean_object* v_r_2226_; 
v_res_2225_ = l_Lean_Syntax_isAntiquots(v_stx_2224_);
v_r_2226_ = lean_box(v_res_2225_);
return v_r_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2227_){
_start:
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2227_);
v___x_2229_ = l_Lean_Syntax_isOfKind(v_stx_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
return v_stx_2227_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = l_Lean_Syntax_getArg(v_stx_2227_, v___x_2230_);
lean_dec(v_stx_2227_);
return v___x_2231_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2234_ = l_Lean_mkAtom(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2238_ = lean_unsigned_to_nat(4u);
v___x_2239_ = lean_mk_empty_array_with_capacity(v___x_2238_);
v___x_2240_ = lean_array_push(v___x_2239_, v___x_2237_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2249_ = l_Lean_mkAtom(v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2251_ = lean_unsigned_to_nat(2u);
v___x_2252_ = lean_mk_empty_array_with_capacity(v___x_2251_);
v___x_2253_ = lean_array_push(v___x_2252_, v___x_2250_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2265_ = l_Lean_mkAtom(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2268_ = l_Lean_mkAtom(v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2269_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2270_ = lean_unsigned_to_nat(3u);
v___x_2271_ = lean_mk_empty_array_with_capacity(v___x_2270_);
v___x_2272_ = lean_array_push(v___x_2271_, v___x_2269_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2273_, lean_object* v_term_2274_, lean_object* v_nesting_2275_, lean_object* v_name_2276_, uint8_t v_isPseudoKind_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v_nesting_2282_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2301_; uint8_t v___x_2309_; 
v___x_2278_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2279_ = lean_mk_array(v_nesting_2275_, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2281_ = lean_box(2);
v_nesting_2282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2282_, 0, v___x_2281_);
lean_ctor_set(v_nesting_2282_, 1, v___x_2280_);
lean_ctor_set(v_nesting_2282_, 2, v___x_2279_);
v___x_2309_ = l_Lean_Syntax_isIdent(v_term_2274_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2274_);
v___x_2311_ = l_Lean_Syntax_isOfKind(v_term_2274_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2312_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2313_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2314_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2315_ = lean_array_push(v___x_2314_, v_term_2274_);
v___x_2316_ = lean_array_push(v___x_2315_, v___x_2313_);
v___x_2317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2281_);
lean_ctor_set(v___x_2317_, 1, v___x_2312_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
v___y_2301_ = v___x_2317_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = l_Lean_Syntax_getArg(v_term_2274_, v___x_2318_);
lean_dec(v_term_2274_);
v___y_2301_ = v___x_2319_;
goto v___jp_2300_;
}
}
else
{
v___y_2301_ = v_term_2274_;
goto v___jp_2300_;
}
v___jp_2283_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_inc(v___y_2286_);
v___x_2287_ = l_Lean_Name_append(v_kind_2273_, v___y_2286_);
v___x_2288_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2289_ = l_Lean_Name_append(v___x_2287_, v___x_2288_);
v___x_2290_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2291_ = lean_array_push(v___x_2290_, v_nesting_2282_);
v___x_2292_ = lean_array_push(v___x_2291_, v___y_2284_);
v___x_2293_ = lean_array_push(v___x_2292_, v___y_2285_);
v___x_2294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2281_);
lean_ctor_set(v___x_2294_, 1, v___x_2289_);
lean_ctor_set(v___x_2294_, 2, v___x_2293_);
return v___x_2294_;
}
v___jp_2295_:
{
if (v_isPseudoKind_2277_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_box(0);
v___y_2284_ = v___y_2296_;
v___y_2285_ = v___y_2297_;
v___y_2286_ = v___x_2298_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2284_ = v___y_2296_;
v___y_2285_ = v___y_2297_;
v___y_2286_ = v___x_2299_;
goto v___jp_2283_;
}
}
v___jp_2300_:
{
if (lean_obj_tag(v_name_2276_) == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2296_ = v___y_2301_;
v___y_2297_ = v___x_2302_;
goto v___jp_2295_;
}
else
{
lean_object* v_val_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_val_2303_ = lean_ctor_get(v_name_2276_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v_name_2276_, 1);
v___x_2304_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2305_ = l_Lean_mkAtom(v_val_2303_);
v___x_2306_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2307_ = lean_array_push(v___x_2306_, v___x_2305_);
v___x_2308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2281_);
lean_ctor_set(v___x_2308_, 1, v___x_2304_);
lean_ctor_set(v___x_2308_, 2, v___x_2307_);
v___y_2296_ = v___y_2301_;
v___y_2297_ = v___x_2308_;
goto v___jp_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2320_, lean_object* v_term_2321_, lean_object* v_nesting_2322_, lean_object* v_name_2323_, lean_object* v_isPseudoKind_2324_){
_start:
{
uint8_t v_isPseudoKind_boxed_2325_; lean_object* v_res_2326_; 
v_isPseudoKind_boxed_2325_ = lean_unbox(v_isPseudoKind_2324_);
v_res_2326_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2320_, v_term_2321_, v_nesting_2322_, v_name_2323_, v_isPseudoKind_boxed_2325_);
return v_res_2326_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2327_){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = l_Lean_Syntax_getArg(v_stx_2327_, v___x_2328_);
v___x_2330_ = l_Lean_Syntax_getArgs(v___x_2329_);
lean_dec(v___x_2329_);
v___x_2331_ = lean_array_get_size(v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_nat_dec_eq(v___x_2331_, v___x_2332_);
v___x_2334_ = lean_bool_not(v___x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2335_){
_start:
{
uint8_t v_res_2336_; lean_object* v_r_2337_; 
v_res_2336_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2335_);
lean_dec(v_stx_2335_);
v_r_2337_ = lean_box(v_res_2336_);
return v_r_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2338_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = l_Lean_Syntax_isAntiquot(v_stx_2338_);
if (v___x_2339_ == 0)
{
return v_stx_2338_;
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = l_Lean_Syntax_getArg(v_stx_2338_, v___x_2340_);
v___x_2342_ = l_Lean_Syntax_getArgs(v___x_2341_);
lean_dec(v___x_2341_);
v___x_2343_ = lean_array_pop(v___x_2342_);
v___x_2344_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2345_ = lean_box(2);
v___x_2346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2344_);
lean_ctor_set(v___x_2346_, 2, v___x_2343_);
v___x_2347_ = l_Lean_Syntax_setArg(v_stx_2338_, v___x_2340_, v___x_2346_);
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2348_){
_start:
{
lean_object* v___y_2350_; uint8_t v___x_2361_; 
v___x_2361_ = l_Lean_Syntax_isAntiquot(v_stx_2348_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(3u);
v___x_2363_ = l_Lean_Syntax_getArg(v_stx_2348_, v___x_2362_);
v___y_2350_ = v___x_2363_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_unsigned_to_nat(2u);
v___x_2365_ = l_Lean_Syntax_getArg(v_stx_2348_, v___x_2364_);
v___y_2350_ = v___x_2365_;
goto v___jp_2349_;
}
v___jp_2349_:
{
uint8_t v___x_2351_; 
v___x_2351_ = l_Lean_Syntax_isIdent(v___y_2350_);
if (v___x_2351_ == 0)
{
uint8_t v___x_2352_; 
v___x_2352_ = l_Lean_Syntax_isAtom(v___y_2350_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = l_Lean_Syntax_getArg(v___y_2350_, v___x_2353_);
lean_dec(v___y_2350_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2355_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2356_ = lean_unsigned_to_nat(1u);
v___x_2357_ = lean_mk_empty_array_with_capacity(v___x_2356_);
v___x_2358_ = lean_array_push(v___x_2357_, v___y_2350_);
v___x_2359_ = lean_box(2);
v___x_2360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
lean_ctor_set(v___x_2360_, 1, v___x_2355_);
lean_ctor_set(v___x_2360_, 2, v___x_2358_);
return v___x_2360_;
}
}
else
{
return v___y_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2366_);
lean_dec(v_stx_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2368_){
_start:
{
if (lean_obj_tag(v_x_2368_) == 1)
{
lean_object* v_kind_2369_; 
v_kind_2369_ = lean_ctor_get(v_x_2368_, 1);
if (lean_obj_tag(v_kind_2369_) == 1)
{
lean_object* v_pre_2370_; lean_object* v_str_2371_; 
v_pre_2370_ = lean_ctor_get(v_kind_2369_, 0);
v_str_2371_ = lean_ctor_get(v_kind_2369_, 1);
if (lean_obj_tag(v_pre_2370_) == 1)
{
lean_object* v_pre_2377_; lean_object* v_str_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_pre_2377_ = lean_ctor_get(v_pre_2370_, 0);
v_str_2378_ = lean_ctor_get(v_pre_2370_, 1);
v___x_2379_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2380_ = lean_string_dec_eq(v_str_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2382_ = lean_string_dec_eq(v_str_2371_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_box(0);
return v___x_2383_;
}
else
{
goto v___jp_2372_;
}
}
else
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2385_ = lean_string_dec_eq(v_str_2371_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_box(0);
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_box(v___x_2385_);
lean_inc(v_pre_2377_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_pre_2377_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
}
else
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2391_ = lean_string_dec_eq(v_str_2371_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_box(0);
return v___x_2392_;
}
else
{
goto v___jp_2372_;
}
}
v___jp_2372_:
{
uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2373_ = 0;
v___x_2374_ = lean_box(v___x_2373_);
lean_inc(v_pre_2370_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v_pre_2370_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
else
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_box(0);
return v___x_2393_;
}
}
else
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_box(0);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2395_);
lean_dec(v_x_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2397_, size_t v_i_2398_, size_t v_stop_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v___y_2402_; uint8_t v___x_2406_; 
v___x_2406_ = lean_usize_dec_eq(v_i_2398_, v_stop_2399_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_array_uget_borrowed(v_as_2397_, v_i_2398_);
v___x_2408_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2407_);
if (lean_obj_tag(v___x_2408_) == 0)
{
v___y_2402_ = v_b_2400_;
goto v___jp_2401_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2410_; 
v_val_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = lean_array_push(v_b_2400_, v_val_2409_);
v___y_2402_ = v___x_2410_;
goto v___jp_2401_;
}
}
else
{
return v_b_2400_;
}
v___jp_2401_:
{
size_t v___x_2403_; size_t v___x_2404_; 
v___x_2403_ = ((size_t)1ULL);
v___x_2404_ = lean_usize_add(v_i_2398_, v___x_2403_);
v_i_2398_ = v___x_2404_;
v_b_2400_ = v___y_2402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2411_, lean_object* v_i_2412_, lean_object* v_stop_2413_, lean_object* v_b_2414_){
_start:
{
size_t v_i_boxed_2415_; size_t v_stop_boxed_2416_; lean_object* v_res_2417_; 
v_i_boxed_2415_ = lean_unbox_usize(v_i_2412_);
lean_dec(v_i_2412_);
v_stop_boxed_2416_ = lean_unbox_usize(v_stop_2413_);
lean_dec(v_stop_2413_);
v_res_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2411_, v_i_boxed_2415_, v_stop_boxed_2416_, v_b_2414_);
lean_dec_ref(v_as_2411_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2420_, lean_object* v_start_2421_, lean_object* v_stop_2422_){
_start:
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2424_ = lean_nat_dec_lt(v_start_2421_, v_stop_2422_);
if (v___x_2424_ == 0)
{
return v___x_2423_;
}
else
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_array_get_size(v_as_2420_);
v___x_2426_ = lean_nat_dec_le(v_stop_2422_, v___x_2425_);
if (v___x_2426_ == 0)
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_nat_dec_lt(v_start_2421_, v___x_2425_);
if (v___x_2427_ == 0)
{
return v___x_2423_;
}
else
{
size_t v___x_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = lean_usize_of_nat(v_start_2421_);
v___x_2429_ = lean_usize_of_nat(v___x_2425_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2420_, v___x_2428_, v___x_2429_, v___x_2423_);
return v___x_2430_;
}
}
else
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_usize_of_nat(v_start_2421_);
v___x_2432_ = lean_usize_of_nat(v_stop_2422_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2420_, v___x_2431_, v___x_2432_, v___x_2423_);
return v___x_2433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2434_, lean_object* v_start_2435_, lean_object* v_stop_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2434_, v_start_2435_, v_stop_2436_);
lean_dec(v_stop_2436_);
lean_dec(v_start_2435_);
lean_dec_ref(v_as_2434_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2438_){
_start:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2438_);
v___x_2440_ = l_Lean_Syntax_isOfKind(v_stx_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2438_);
lean_dec(v_stx_2438_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_box(0);
return v___x_2442_;
}
else
{
lean_object* v_val_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_val_2443_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_val_2443_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2445_, 0, v_val_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
return v___x_2445_;
}
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2446_ = l_Lean_Syntax_getArgs(v_stx_2438_);
lean_dec(v_stx_2438_);
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2448_ = lean_array_get_size(v___x_2446_);
v___x_2449_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2446_, v___x_2447_, v___x_2448_);
lean_dec_ref(v___x_2446_);
v___x_2450_ = lean_array_to_list(v___x_2449_);
return v___x_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 1)
{
lean_object* v_kind_2453_; 
v_kind_2453_ = lean_ctor_get(v_x_2452_, 1);
if (lean_obj_tag(v_kind_2453_) == 1)
{
lean_object* v_pre_2454_; lean_object* v_str_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v_pre_2454_ = lean_ctor_get(v_kind_2453_, 0);
v_str_2455_ = lean_ctor_get(v_kind_2453_, 1);
v___x_2456_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2457_ = lean_string_dec_eq(v_str_2455_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_box(0);
return v___x_2458_;
}
else
{
lean_object* v___x_2459_; 
lean_inc(v_pre_2454_);
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_pre_2454_);
return v___x_2459_;
}
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_box(0);
return v___x_2460_;
}
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_box(0);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2462_);
lean_dec(v_x_2462_);
return v_res_2463_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2464_);
if (lean_obj_tag(v___x_2465_) == 0)
{
uint8_t v___x_2466_; 
v___x_2466_ = 0;
return v___x_2466_;
}
else
{
uint8_t v___x_2467_; 
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = 1;
return v___x_2467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2468_){
_start:
{
uint8_t v_res_2469_; lean_object* v_r_2470_; 
v_res_2469_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2468_);
lean_dec(v_stx_2468_);
v_r_2470_ = lean_box(v_res_2469_);
return v_r_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2471_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_unsigned_to_nat(3u);
v___x_2473_ = l_Lean_Syntax_getArg(v_stx_2471_, v___x_2472_);
v___x_2474_ = l_Lean_Syntax_getArgs(v___x_2473_);
lean_dec(v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2475_);
lean_dec(v_stx_2475_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2477_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = l_Lean_Syntax_getArg(v_stx_2477_, v___x_2479_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_unsigned_to_nat(5u);
v___x_2482_ = l_Lean_Syntax_getArg(v_stx_2477_, v___x_2481_);
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2483_);
lean_dec(v_stx_2483_);
return v_res_2484_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2490_ = l_Lean_mkAtom(v___x_2489_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2493_ = l_Lean_mkAtom(v___x_2492_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2495_ = lean_unsigned_to_nat(6u);
v___x_2496_ = lean_mk_empty_array_with_capacity(v___x_2495_);
v___x_2497_ = lean_array_push(v___x_2496_, v___x_2494_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2498_, lean_object* v_contents_2499_, lean_object* v_suffix_2500_, lean_object* v_nesting_2501_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v_nesting_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2502_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2503_ = lean_mk_array(v_nesting_2501_, v___x_2502_);
v___x_2504_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2505_ = lean_box(2);
v_nesting_2506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2506_, 0, v___x_2505_);
lean_ctor_set(v_nesting_2506_, 1, v___x_2504_);
lean_ctor_set(v_nesting_2506_, 2, v___x_2503_);
v___x_2507_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2508_ = l_Lean_Name_append(v_kind_2498_, v___x_2507_);
v___x_2509_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2505_);
lean_ctor_set(v___x_2510_, 1, v___x_2504_);
lean_ctor_set(v___x_2510_, 2, v_contents_2499_);
v___x_2511_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2512_ = l_Lean_mkAtom(v_suffix_2500_);
v___x_2513_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2514_ = lean_array_push(v___x_2513_, v_nesting_2506_);
v___x_2515_ = lean_array_push(v___x_2514_, v___x_2509_);
v___x_2516_ = lean_array_push(v___x_2515_, v___x_2510_);
v___x_2517_ = lean_array_push(v___x_2516_, v___x_2511_);
v___x_2518_ = lean_array_push(v___x_2517_, v___x_2512_);
v___x_2519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2505_);
lean_ctor_set(v___x_2519_, 1, v___x_2508_);
lean_ctor_set(v___x_2519_, 2, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2521_){
_start:
{
if (lean_obj_tag(v_x_2521_) == 1)
{
lean_object* v_kind_2522_; 
v_kind_2522_ = lean_ctor_get(v_x_2521_, 1);
if (lean_obj_tag(v_kind_2522_) == 1)
{
lean_object* v_pre_2523_; lean_object* v_str_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_pre_2523_ = lean_ctor_get(v_kind_2522_, 0);
v_str_2524_ = lean_ctor_get(v_kind_2522_, 1);
v___x_2525_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2526_ = lean_string_dec_eq(v_str_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_box(0);
return v___x_2527_;
}
else
{
lean_object* v___x_2528_; 
lean_inc(v_pre_2523_);
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_pre_2523_);
return v___x_2528_;
}
}
else
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_box(0);
return v___x_2529_;
}
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_box(0);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2531_);
lean_dec(v_x_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2533_);
if (lean_obj_tag(v___x_2534_) == 0)
{
uint8_t v___x_2535_; 
v___x_2535_ = 0;
return v___x_2535_;
}
else
{
uint8_t v___x_2536_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = 1;
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2537_){
_start:
{
uint8_t v_res_2538_; lean_object* v_r_2539_; 
v_res_2538_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2537_);
lean_dec(v_stx_2537_);
v_r_2539_ = lean_box(v_res_2538_);
return v_r_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2540_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = l_Lean_Syntax_getArg(v_stx_2540_, v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2543_);
lean_dec(v_stx_2543_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2547_, lean_object* v_inner_2548_, lean_object* v_suffix_2549_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2550_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2551_ = l_Lean_Name_append(v_kind_2547_, v___x_2550_);
v___x_2552_ = l_Lean_mkAtom(v_suffix_2549_);
v___x_2553_ = lean_unsigned_to_nat(2u);
v___x_2554_ = lean_mk_empty_array_with_capacity(v___x_2553_);
v___x_2555_ = lean_array_push(v___x_2554_, v_inner_2548_);
v___x_2556_ = lean_array_push(v___x_2555_, v___x_2552_);
v___x_2557_ = lean_box(2);
v___x_2558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
lean_ctor_set(v___x_2558_, 1, v___x_2551_);
lean_ctor_set(v___x_2558_, 2, v___x_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2562_){
_start:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2564_ = l_Lean_Syntax_isOfKind(v_stx_2562_, v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2565_){
_start:
{
uint8_t v_res_2566_; lean_object* v_r_2567_; 
v_res_2566_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2565_);
v_r_2567_ = lean_box(v_res_2566_);
return v_r_2567_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2568_){
_start:
{
uint8_t v___y_2570_; uint8_t v___x_2573_; 
v___x_2573_ = l_Lean_Syntax_isAntiquot(v_stx_2568_);
if (v___x_2573_ == 0)
{
uint8_t v___x_2574_; 
v___x_2574_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2568_);
v___y_2570_ = v___x_2574_;
goto v___jp_2569_;
}
else
{
v___y_2570_ = v___x_2573_;
goto v___jp_2569_;
}
v___jp_2569_:
{
if (v___y_2570_ == 0)
{
uint8_t v___x_2571_; 
v___x_2571_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2568_);
if (v___x_2571_ == 0)
{
uint8_t v___x_2572_; 
v___x_2572_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2568_);
return v___x_2572_;
}
else
{
lean_dec(v_stx_2568_);
return v___x_2571_;
}
}
else
{
lean_dec(v_stx_2568_);
return v___y_2570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2575_){
_start:
{
uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_res_2576_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2575_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2581_, lean_object* v_stx_2582_, lean_object* v_visit_2583_, lean_object* v_stack_2584_, lean_object* v_accept_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v_a_2589_; uint8_t v___x_2593_; 
v___x_2593_ = lean_nat_dec_lt(v_a_2586_, v_upperBound_2581_);
if (v___x_2593_ == 0)
{
lean_dec(v_a_2586_);
lean_dec_ref(v_accept_2585_);
lean_dec(v_stack_2584_);
lean_dec_ref(v_visit_2583_);
lean_dec(v_stx_2582_);
lean_inc_ref(v_b_2587_);
return v_b_2587_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2596_ = l_Lean_Syntax_getArg(v_stx_2582_, v_a_2586_);
lean_inc_ref(v_visit_2583_);
lean_inc(v___x_2596_);
v___x_2597_ = lean_apply_1(v_visit_2583_, v___x_2596_);
v___x_2598_ = lean_unbox(v___x_2597_);
if (v___x_2598_ == 0)
{
lean_dec(v___x_2596_);
v_a_2589_ = v___x_2595_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_inc(v_a_2586_);
lean_inc(v_stx_2582_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_stx_2582_);
lean_ctor_set(v___x_2599_, 1, v_a_2586_);
lean_inc(v_stack_2584_);
v___x_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v_stack_2584_);
lean_inc_ref(v_accept_2585_);
lean_inc_ref(v_visit_2583_);
v___x_2601_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2583_, v_accept_2585_, v___x_2600_, v___x_2596_);
if (lean_obj_tag(v___x_2601_) == 1)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec(v_a_2586_);
lean_dec_ref(v_accept_2585_);
lean_dec(v_stack_2584_);
lean_dec_ref(v_visit_2583_);
lean_dec(v_stx_2582_);
v___x_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___x_2594_);
return v___x_2603_;
}
else
{
lean_dec(v___x_2601_);
v_a_2589_ = v___x_2595_;
goto v___jp_2588_;
}
}
}
v___jp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_nat_add(v_a_2586_, v___x_2590_);
lean_dec(v_a_2586_);
v_a_2586_ = v___x_2591_;
v_b_2587_ = v_a_2589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2604_, lean_object* v_accept_2605_, lean_object* v_stack_2606_, lean_object* v_stx_2607_){
_start:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
lean_inc_ref(v_accept_2605_);
lean_inc(v_stx_2607_);
v___x_2608_ = lean_apply_1(v_accept_2605_, v_stx_2607_);
v___x_2609_ = lean_unbox(v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v_fst_2615_; 
v___x_2610_ = l_Lean_Syntax_getNumArgs(v_stx_2607_);
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_box(0);
v___x_2613_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2614_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2610_, v_stx_2607_, v_visit_2604_, v_stack_2606_, v_accept_2605_, v___x_2611_, v___x_2613_);
lean_dec(v___x_2610_);
v_fst_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_fst_2615_);
lean_dec_ref(v___x_2614_);
if (lean_obj_tag(v_fst_2615_) == 0)
{
return v___x_2612_;
}
else
{
lean_object* v_val_2616_; 
v_val_2616_ = lean_ctor_get(v_fst_2615_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v_fst_2615_, 1);
return v_val_2616_;
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec_ref(v_accept_2605_);
lean_dec_ref(v_visit_2604_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_stx_2607_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v_stack_2606_);
v___x_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2621_, lean_object* v_stx_2622_, lean_object* v_visit_2623_, lean_object* v_stack_2624_, lean_object* v_accept_2625_, lean_object* v_a_2626_, lean_object* v_b_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2621_, v_stx_2622_, v_visit_2623_, v_stack_2624_, v_accept_2625_, v_a_2626_, v_b_2627_);
lean_dec_ref(v_b_2627_);
lean_dec(v_upperBound_2621_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2629_, lean_object* v_stx_2630_, lean_object* v_visit_2631_, lean_object* v_stack_2632_, lean_object* v_accept_2633_, lean_object* v_inst_2634_, lean_object* v_R_2635_, lean_object* v_a_2636_, lean_object* v_b_2637_, lean_object* v_c_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2629_, v_stx_2630_, v_visit_2631_, v_stack_2632_, v_accept_2633_, v_a_2636_, v_b_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2640_, lean_object* v_stx_2641_, lean_object* v_visit_2642_, lean_object* v_stack_2643_, lean_object* v_accept_2644_, lean_object* v_inst_2645_, lean_object* v_R_2646_, lean_object* v_a_2647_, lean_object* v_b_2648_, lean_object* v_c_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2640_, v_stx_2641_, v_visit_2642_, v_stack_2643_, v_accept_2644_, v_inst_2645_, v_R_2646_, v_a_2647_, v_b_2648_, v_c_2649_);
lean_dec_ref(v_b_2648_);
lean_dec(v_upperBound_2640_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2651_, lean_object* v_visit_2652_, lean_object* v_accept_2653_){
_start:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
lean_inc_ref(v_visit_2652_);
lean_inc(v_root_2651_);
v___x_2654_ = lean_apply_1(v_visit_2652_, v_root_2651_);
v___x_2655_ = lean_unbox(v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v_accept_2653_);
lean_dec_ref(v_visit_2652_);
lean_dec(v_root_2651_);
v___x_2656_ = lean_box(0);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2652_, v_accept_2653_, v___x_2657_, v_root_2651_);
return v___x_2658_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2659_, lean_object* v_x_2660_, lean_object* v_p_2661_){
_start:
{
if (lean_obj_tag(v_p_2661_) == 0)
{
lean_dec_ref(v_x_2660_);
return v___x_2659_;
}
else
{
lean_object* v_fst_2662_; lean_object* v_val_2663_; uint8_t v___x_2664_; 
v_fst_2662_ = lean_ctor_get(v_x_2660_, 0);
lean_inc(v_fst_2662_);
lean_dec_ref(v_x_2660_);
v_val_2663_ = lean_ctor_get(v_p_2661_, 0);
v___x_2664_ = l_Lean_Syntax_isOfKind(v_fst_2662_, v_val_2663_);
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2665_, lean_object* v_x_2666_, lean_object* v_p_2667_){
_start:
{
uint8_t v___x_121__boxed_2668_; uint8_t v_res_2669_; lean_object* v_r_2670_; 
v___x_121__boxed_2668_ = lean_unbox(v___x_2665_);
v_res_2669_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_121__boxed_2668_, v_x_2666_, v_p_2667_);
lean_dec(v_p_2667_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2671_){
_start:
{
if (lean_obj_tag(v_x_2671_) == 0)
{
uint8_t v___x_2672_; 
v___x_2672_ = 1;
return v___x_2672_;
}
else
{
lean_object* v_head_2673_; uint8_t v___x_2674_; 
v_head_2673_ = lean_ctor_get(v_x_2671_, 0);
v___x_2674_ = lean_unbox(v_head_2673_);
if (v___x_2674_ == 0)
{
uint8_t v___x_2675_; 
v___x_2675_ = lean_unbox(v_head_2673_);
return v___x_2675_;
}
else
{
lean_object* v_tail_2676_; 
v_tail_2676_ = lean_ctor_get(v_x_2671_, 1);
v_x_2671_ = v_tail_2676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2678_){
_start:
{
uint8_t v_res_2679_; lean_object* v_r_2680_; 
v_res_2679_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2678_);
lean_dec(v_x_2678_);
v_r_2680_ = lean_box(v_res_2679_);
return v_r_2680_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2683_, lean_object* v_pattern_2684_){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = l_List_lengthTR___redArg(v_pattern_2684_);
v___x_2686_ = l_List_lengthTR___redArg(v_stack_2683_);
v___x_2687_ = lean_nat_dec_le(v___x_2685_, v___x_2686_);
lean_dec(v___x_2686_);
lean_dec(v___x_2685_);
if (v___x_2687_ == 0)
{
lean_dec(v_pattern_2684_);
lean_dec(v_stack_2683_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; lean_object* v___f_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2688_ = lean_box(v___x_2687_);
v___f_2689_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2689_, 0, v___x_2688_);
v___x_2690_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2691_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2689_, v_stack_2683_, v_pattern_2684_, v___x_2690_);
v___x_2692_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2691_);
lean_dec(v___x_2691_);
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2693_, lean_object* v_pattern_2694_){
_start:
{
uint8_t v_res_2695_; lean_object* v_r_2696_; 
v_res_2695_ = l_Lean_Syntax_Stack_matches(v_stack_2693_, v_pattern_2694_);
v_r_2696_ = lean_box(v_res_2695_);
return v_r_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2697_, lean_object* v_trailing_2698_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2697_);
if (lean_obj_tag(v___x_2699_) == 1)
{
lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2735_; 
v_val_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2735_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2735_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
if (lean_obj_tag(v_val_2700_) == 0)
{
lean_object* v_trailing_2704_; lean_object* v_leading_2705_; lean_object* v_pos_2706_; lean_object* v_endPos_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2733_; 
v_trailing_2704_ = lean_ctor_get(v_val_2700_, 2);
v_leading_2705_ = lean_ctor_get(v_val_2700_, 0);
v_pos_2706_ = lean_ctor_get(v_val_2700_, 1);
v_endPos_2707_ = lean_ctor_get(v_val_2700_, 3);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_val_2700_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2709_ = v_val_2700_;
v_isShared_2710_ = v_isSharedCheck_2733_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_endPos_2707_);
lean_inc(v_trailing_2704_);
lean_inc(v_pos_2706_);
lean_inc(v_leading_2705_);
lean_dec(v_val_2700_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2733_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_str_2711_; lean_object* v_startPos_2712_; lean_object* v_stopPos_2713_; lean_object* v_startPos_2714_; lean_object* v_stopPos_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2731_; 
v_str_2711_ = lean_ctor_get(v_trailing_2704_, 0);
lean_inc_ref(v_str_2711_);
v_startPos_2712_ = lean_ctor_get(v_trailing_2704_, 1);
lean_inc(v_startPos_2712_);
v_stopPos_2713_ = lean_ctor_get(v_trailing_2704_, 2);
lean_inc(v_stopPos_2713_);
lean_dec_ref(v_trailing_2704_);
v_startPos_2714_ = lean_ctor_get(v_trailing_2698_, 1);
v_stopPos_2715_ = lean_ctor_get(v_trailing_2698_, 2);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_trailing_2698_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v_trailing_2698_, 0);
lean_dec(v_unused_2732_);
v___x_2717_ = v_trailing_2698_;
v_isShared_2718_ = v_isSharedCheck_2731_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_stopPos_2715_);
lean_inc(v_startPos_2714_);
lean_dec(v_trailing_2698_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2731_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_nat_dec_eq(v_stopPos_2713_, v_startPos_2714_);
lean_dec(v_startPos_2714_);
lean_dec(v_stopPos_2713_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_del_object(v___x_2717_);
lean_dec(v_stopPos_2715_);
lean_dec(v_startPos_2712_);
lean_dec_ref(v_str_2711_);
lean_del_object(v___x_2709_);
lean_dec(v_endPos_2707_);
lean_dec(v_pos_2706_);
lean_dec_ref(v_leading_2705_);
lean_del_object(v___x_2702_);
lean_dec(v_stx_2697_);
v___x_2720_ = lean_box(0);
return v___x_2720_;
}
else
{
lean_object* v_trailing_2722_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v_startPos_2712_);
lean_ctor_set(v___x_2717_, 0, v_str_2711_);
v_trailing_2722_ = v___x_2717_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_str_2711_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_startPos_2712_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_stopPos_2715_);
v_trailing_2722_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 2, v_trailing_2722_);
v___x_2724_ = v___x_2709_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_leading_2705_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_pos_2706_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_trailing_2722_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_endPos_2707_);
v___x_2724_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = l_Lean_Syntax_setTailInfo(v_stx_2697_, v___x_2724_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2725_);
v___x_2727_ = v___x_2702_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2734_; 
lean_del_object(v___x_2702_);
lean_dec(v_val_2700_);
lean_dec_ref(v_trailing_2698_);
lean_dec(v_stx_2697_);
v___x_2734_ = lean_box(0);
return v___x_2734_;
}
}
}
else
{
lean_object* v___x_2736_; 
lean_dec(v___x_2699_);
lean_dec_ref(v_trailing_2698_);
lean_dec(v_stx_2697_);
v___x_2736_ = lean_box(0);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2737_, lean_object* v_trailing_2738_){
_start:
{
lean_object* v___x_2739_; 
lean_inc(v_stx_2737_);
v___x_2739_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2737_, v_trailing_2738_);
if (lean_obj_tag(v___x_2739_) == 0)
{
return v_stx_2737_;
}
else
{
lean_object* v_val_2740_; 
lean_dec(v_stx_2737_);
v_val_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_val_2740_);
lean_dec_ref_known(v___x_2739_, 1);
return v_val_2740_;
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

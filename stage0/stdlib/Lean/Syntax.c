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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_identComponents_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_identComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_getAtomVal___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__1_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__2 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__2_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.identComponents\?"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__3 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__3_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__4 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Syntax_identComponents_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents_x3f___closed__5;
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
lean_object* v_start_140_; lean_object* v_stop_141_; lean_object* v_start_142_; lean_object* v_stop_143_; uint8_t v___y_145_; uint8_t v___x_151_; uint8_t v___y_153_; 
v_start_140_ = lean_ctor_get(v_super_136_, 0);
v_stop_141_ = lean_ctor_get(v_super_136_, 1);
v_start_142_ = lean_ctor_get(v_sub_137_, 0);
v_stop_143_ = lean_ctor_get(v_sub_137_, 1);
v___x_151_ = lean_nat_dec_le(v_start_140_, v_start_142_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
if (v_includeSuperStop_138_ == 0)
{
v___y_153_ = v_includeSuperStop_138_;
goto v___jp_152_;
}
else
{
if (v_includeSubStop_139_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_stop_141_, v___x_154_);
v___x_156_ = lean_nat_dec_le(v_stop_143_, v___x_155_);
lean_dec(v___x_155_);
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
v___y_153_ = v___x_157_;
goto v___jp_152_;
}
}
}
v___jp_144_:
{
if (v___y_145_ == 0)
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_le(v_stop_143_, v_stop_141_);
return v___x_146_;
}
else
{
if (v_includeSubStop_139_ == 0)
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_le(v_stop_143_, v_stop_141_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_stop_143_, v___x_148_);
v___x_150_ = lean_nat_dec_le(v___x_149_, v_stop_141_);
lean_dec(v___x_149_);
return v___x_150_;
}
}
}
v___jp_152_:
{
if (v_includeSuperStop_138_ == 0)
{
v___y_145_ = v___x_151_;
goto v___jp_144_;
}
else
{
v___y_145_ = v___y_153_;
goto v___jp_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_158_, lean_object* v_sub_159_, lean_object* v_includeSuperStop_160_, lean_object* v_includeSubStop_161_){
_start:
{
uint8_t v_includeSuperStop_boxed_162_; uint8_t v_includeSubStop_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_includeSuperStop_boxed_162_ = lean_unbox(v_includeSuperStop_160_);
v_includeSubStop_boxed_163_ = lean_unbox(v_includeSubStop_161_);
v_res_164_ = l_Lean_Syntax_Range_includes(v_super_158_, v_sub_159_, v_includeSuperStop_boxed_162_, v_includeSubStop_boxed_163_);
lean_dec_ref(v_sub_159_);
lean_dec_ref(v_super_158_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_166_, lean_object* v_second_167_, uint8_t v_includeFirstStop_168_, uint8_t v_includeSecondStop_169_){
_start:
{
uint8_t v___y_171_; 
if (v_includeFirstStop_168_ == 0)
{
lean_object* v_start_180_; lean_object* v_stop_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_start_180_ = lean_ctor_get(v_second_167_, 0);
v_stop_181_ = lean_ctor_get(v_first_166_, 1);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_start_180_, v___x_182_);
v___x_184_ = lean_nat_dec_le(v___x_183_, v_stop_181_);
lean_dec(v___x_183_);
v___y_171_ = v___x_184_;
goto v___jp_170_;
}
else
{
lean_object* v_start_185_; lean_object* v_stop_186_; uint8_t v___x_187_; 
v_start_185_ = lean_ctor_get(v_second_167_, 0);
v_stop_186_ = lean_ctor_get(v_first_166_, 1);
v___x_187_ = lean_nat_dec_le(v_start_185_, v_stop_186_);
v___y_171_ = v___x_187_;
goto v___jp_170_;
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
return v___y_171_;
}
else
{
if (v_includeSecondStop_169_ == 0)
{
lean_object* v_start_172_; lean_object* v_stop_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_start_172_ = lean_ctor_get(v_first_166_, 0);
v_stop_173_ = lean_ctor_get(v_second_167_, 1);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_start_172_, v___x_174_);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_stop_173_);
lean_dec(v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_start_177_; lean_object* v_stop_178_; uint8_t v___x_179_; 
v_start_177_ = lean_ctor_get(v_first_166_, 0);
v_stop_178_ = lean_ctor_get(v_second_167_, 1);
v___x_179_ = lean_nat_dec_le(v_start_177_, v_stop_178_);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object* v_first_188_, lean_object* v_second_189_, lean_object* v_includeFirstStop_190_, lean_object* v_includeSecondStop_191_){
_start:
{
uint8_t v_includeFirstStop_boxed_192_; uint8_t v_includeSecondStop_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_includeFirstStop_boxed_192_ = lean_unbox(v_includeFirstStop_190_);
v_includeSecondStop_boxed_193_ = lean_unbox(v_includeSecondStop_191_);
v_res_194_ = l_Lean_Syntax_Range_overlaps(v_first_188_, v_second_189_, v_includeFirstStop_boxed_192_, v_includeSecondStop_boxed_193_);
lean_dec_ref(v_second_189_);
lean_dec_ref(v_first_188_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_196_){
_start:
{
lean_object* v_start_197_; lean_object* v_stop_198_; lean_object* v___x_199_; 
v_start_197_ = lean_ctor_get(v_r_196_, 0);
v_stop_198_ = lean_ctor_get(v_r_196_, 1);
v___x_199_ = lean_nat_sub(v_stop_198_, v_start_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Syntax_Range_bsize(v_r_200_);
lean_dec_ref(v_r_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v_leading_204_; lean_object* v_pos_205_; lean_object* v_endPos_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_leading_204_ = lean_ctor_get(v_x_203_, 0);
v_pos_205_ = lean_ctor_get(v_x_203_, 1);
v_endPos_206_ = lean_ctor_get(v_x_203_, 3);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_x_203_, 2);
lean_dec(v_unused_214_);
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_endPos_206_);
lean_inc(v_pos_205_);
lean_inc(v_leading_204_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 2, v_trailing_202_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_leading_204_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_pos_205_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_trailing_202_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_endPos_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_dec_ref(v_trailing_202_);
return v_x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_215_, lean_object* v_info_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_SourceInfo_getPos_x3f(v_info_216_, v_canonicalOnly_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v___x_220_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_217_, 1);
v___x_220_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_216_, v_canonicalOnly_215_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
lean_dec(v_val_219_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_val_219_);
lean_ctor_set(v___x_226_, 1, v_val_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_231_, lean_object* v_info_232_){
_start:
{
uint8_t v_canonicalOnly_boxed_233_; lean_object* v_res_234_; 
v_canonicalOnly_boxed_233_ = lean_unbox(v_canonicalOnly_231_);
v_res_234_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_233_, v_info_232_);
lean_dec(v_info_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_235_, lean_object* v_info_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_SourceInfo_getPos_x3f(v_info_236_, v_canonicalOnly_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_240_; 
v_val_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v___x_237_, 1);
v___x_240_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_236_, v_canonicalOnly_235_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_dec(v_val_239_);
v___x_241_ = lean_box(0);
return v___x_241_;
}
else
{
lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_250_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_250_ == 0)
{
v___x_244_ = v___x_240_;
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_dec(v___x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_val_239_);
lean_ctor_set(v___x_246_, 1, v_val_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_251_, lean_object* v_info_252_){
_start:
{
uint8_t v_canonicalOnly_boxed_253_; lean_object* v_res_254_; 
v_canonicalOnly_boxed_253_ = lean_unbox(v_canonicalOnly_251_);
v_res_254_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_253_, v_info_252_);
lean_dec(v_info_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_255_){
_start:
{
switch(lean_obj_tag(v_x_255_))
{
case 0:
{
lean_object* v_pos_256_; lean_object* v_endPos_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v_pos_256_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_pos_256_);
v_endPos_257_ = lean_ctor_get(v_x_255_, 3);
lean_inc(v_endPos_257_);
lean_dec_ref_known(v_x_255_, 4);
v___x_258_ = 0;
v___x_259_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_259_, 0, v_pos_256_);
lean_ctor_set(v___x_259_, 1, v_endPos_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*2, v___x_258_);
return v___x_259_;
}
case 1:
{
lean_object* v_pos_260_; lean_object* v_endPos_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_pos_260_ = lean_ctor_get(v_x_255_, 0);
v_endPos_261_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v_x_255_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_endPos_261_);
lean_inc(v_pos_260_);
lean_dec(v_x_255_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
uint8_t v___x_265_; lean_object* v___x_267_; 
v___x_265_ = 0;
if (v_isShared_264_ == 0)
{
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_pos_260_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_endPos_261_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*2, v___x_265_);
return v___x_267_;
}
}
}
default: 
{
return v_x_255_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
switch(lean_obj_tag(v_x_270_))
{
case 0:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_leading_272_; lean_object* v_pos_273_; lean_object* v_trailing_274_; lean_object* v_endPos_275_; lean_object* v_leading_276_; lean_object* v_pos_277_; lean_object* v_trailing_278_; lean_object* v_endPos_279_; uint8_t v___x_280_; 
v_leading_272_ = lean_ctor_get(v_x_270_, 0);
lean_inc_ref(v_leading_272_);
v_pos_273_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_pos_273_);
v_trailing_274_ = lean_ctor_get(v_x_270_, 2);
lean_inc_ref(v_trailing_274_);
v_endPos_275_ = lean_ctor_get(v_x_270_, 3);
lean_inc(v_endPos_275_);
lean_dec_ref_known(v_x_270_, 4);
v_leading_276_ = lean_ctor_get(v_x_271_, 0);
lean_inc_ref(v_leading_276_);
v_pos_277_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_pos_277_);
v_trailing_278_ = lean_ctor_get(v_x_271_, 2);
lean_inc_ref(v_trailing_278_);
v_endPos_279_ = lean_ctor_get(v_x_271_, 3);
lean_inc(v_endPos_279_);
lean_dec_ref_known(v_x_271_, 4);
v___x_280_ = l_Substring_Raw_beq(v_leading_272_, v_leading_276_);
if (v___x_280_ == 0)
{
lean_dec(v_endPos_279_);
lean_dec_ref(v_trailing_278_);
lean_dec(v_pos_277_);
lean_dec(v_endPos_275_);
lean_dec_ref(v_trailing_274_);
lean_dec(v_pos_273_);
return v___x_280_;
}
else
{
uint8_t v_decide_281_; 
v_decide_281_ = lean_nat_dec_eq(v_pos_273_, v_pos_277_);
lean_dec(v_pos_277_);
lean_dec(v_pos_273_);
if (v_decide_281_ == 0)
{
lean_dec(v_endPos_279_);
lean_dec_ref(v_trailing_278_);
lean_dec(v_endPos_275_);
lean_dec_ref(v_trailing_274_);
return v_decide_281_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = l_Substring_Raw_beq(v_trailing_274_, v_trailing_278_);
if (v___x_282_ == 0)
{
lean_dec(v_endPos_279_);
lean_dec(v_endPos_275_);
return v___x_282_;
}
else
{
uint8_t v_decide_283_; 
v_decide_283_ = lean_nat_dec_eq(v_endPos_275_, v_endPos_279_);
lean_dec(v_endPos_279_);
lean_dec(v_endPos_275_);
return v_decide_283_;
}
}
}
}
else
{
uint8_t v___x_284_; 
lean_dec_ref_known(v_x_270_, 4);
lean_dec(v_x_271_);
v___x_284_ = 0;
return v___x_284_;
}
}
case 1:
{
if (lean_obj_tag(v_x_271_) == 1)
{
lean_object* v_pos_285_; lean_object* v_endPos_286_; uint8_t v_canonical_287_; lean_object* v_pos_288_; lean_object* v_endPos_289_; uint8_t v_canonical_290_; uint8_t v_decide_291_; 
v_pos_285_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_pos_285_);
v_endPos_286_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_endPos_286_);
v_canonical_287_ = lean_ctor_get_uint8(v_x_270_, sizeof(void*)*2);
lean_dec_ref_known(v_x_270_, 2);
v_pos_288_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_pos_288_);
v_endPos_289_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_endPos_289_);
v_canonical_290_ = lean_ctor_get_uint8(v_x_271_, sizeof(void*)*2);
lean_dec_ref_known(v_x_271_, 2);
v_decide_291_ = lean_nat_dec_eq(v_pos_285_, v_pos_288_);
lean_dec(v_pos_288_);
lean_dec(v_pos_285_);
if (v_decide_291_ == 0)
{
lean_dec(v_endPos_289_);
lean_dec(v_endPos_286_);
return v_decide_291_;
}
else
{
uint8_t v_decide_292_; 
v_decide_292_ = lean_nat_dec_eq(v_endPos_286_, v_endPos_289_);
lean_dec(v_endPos_289_);
lean_dec(v_endPos_286_);
if (v_decide_292_ == 0)
{
return v_decide_292_;
}
else
{
if (v_canonical_290_ == 0)
{
if (v_canonical_287_ == 0)
{
return v_decide_292_;
}
else
{
return v_canonical_290_;
}
}
else
{
return v_canonical_287_;
}
}
}
}
else
{
uint8_t v___x_293_; 
lean_dec_ref_known(v_x_270_, 2);
lean_dec(v_x_271_);
v___x_293_ = 0;
return v___x_293_;
}
}
default: 
{
if (lean_obj_tag(v_x_271_) == 2)
{
uint8_t v___x_294_; 
v___x_294_ = 1;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
lean_dec(v_x_271_);
v___x_295_ = 0;
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_296_, v_x_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg___boxed(lean_object* v___dummy_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_unreachIsNodeMissing___redArg();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_305_, lean_object* v_a_306_){
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
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___redArg___boxed(lean_object* v___dummy_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_unreachIsNodeAtom___redArg();
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_310_, lean_object* v_info_311_, lean_object* v_val_312_, lean_object* v_a_313_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_314_, lean_object* v_info_315_, lean_object* v_val_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_314_, v_info_315_, v_val_316_, v_a_317_);
lean_dec_ref(v_val_316_);
lean_dec(v_info_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg___boxed(lean_object* v___dummy_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_unreachIsNodeIdent___redArg();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_322_, lean_object* v_info_323_, lean_object* v_rawVal_324_, lean_object* v_val_325_, lean_object* v_preresolved_326_, lean_object* v_a_327_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_328_, lean_object* v_info_329_, lean_object* v_rawVal_330_, lean_object* v_val_331_, lean_object* v_preresolved_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_328_, v_info_329_, v_rawVal_330_, v_val_331_, v_preresolved_332_, v_a_333_);
lean_dec(v_preresolved_332_);
lean_dec(v_val_331_);
lean_dec_ref(v_rawVal_330_);
lean_dec(v_info_329_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object* v_k_350_){
_start:
{
uint8_t v___y_352_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_360_ = lean_name_eq(v_k_350_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_362_ = lean_name_eq(v_k_350_, v___x_361_);
v___y_352_ = v___x_362_;
goto v___jp_351_;
}
else
{
v___y_352_ = v___x_360_;
goto v___jp_351_;
}
v___jp_351_:
{
if (v___y_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_354_ = lean_name_eq(v_k_350_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_356_ = lean_name_eq(v_k_350_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_358_ = lean_name_eq(v_k_350_, v___x_357_);
return v___x_358_;
}
else
{
return v___x_356_;
}
}
else
{
return v___x_354_;
}
}
else
{
return v___y_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Lean_isLitKind(v_k_363_);
lean_dec(v_k_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_366_){
_start:
{
lean_object* v_kind_367_; 
v_kind_367_ = lean_ctor_get(v_n_366_, 1);
lean_inc(v_kind_367_);
return v_kind_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_SyntaxNode_getKind(v_n_368_);
lean_dec(v_n_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_370_, lean_object* v_fn_371_){
_start:
{
lean_object* v_args_372_; lean_object* v___x_373_; 
v_args_372_ = lean_ctor_get(v_n_370_, 2);
lean_inc_ref(v_args_372_);
lean_dec(v_n_370_);
v___x_373_ = lean_apply_1(v_fn_371_, v_args_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_374_, lean_object* v_n_375_, lean_object* v_fn_376_){
_start:
{
lean_object* v_args_377_; lean_object* v___x_378_; 
v_args_377_ = lean_ctor_get(v_n_375_, 2);
lean_inc_ref(v_args_377_);
lean_dec(v_n_375_);
v___x_378_ = lean_apply_1(v_fn_376_, v_args_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_379_){
_start:
{
lean_object* v_args_380_; lean_object* v___x_381_; 
v_args_380_ = lean_ctor_get(v_n_379_, 2);
v___x_381_ = lean_array_get_size(v_args_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_SyntaxNode_getNumArgs(v_n_382_);
lean_dec(v_n_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_384_, lean_object* v_i_385_){
_start:
{
lean_object* v_args_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_args_386_ = lean_ctor_get(v_n_384_, 2);
v___x_387_ = lean_box(0);
v___x_388_ = lean_array_get_borrowed(v___x_387_, v_args_386_, v_i_385_);
lean_inc(v___x_388_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_389_, lean_object* v_i_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_SyntaxNode_getArg(v_n_389_, v_i_390_);
lean_dec(v_i_390_);
lean_dec(v_n_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_392_){
_start:
{
lean_object* v_args_393_; 
v_args_393_ = lean_ctor_get(v_n_392_, 2);
lean_inc_ref(v_args_393_);
return v_args_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_SyntaxNode_getArgs(v_n_394_);
lean_dec(v_n_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_396_, lean_object* v_fn_397_){
_start:
{
lean_object* v_info_398_; lean_object* v_kind_399_; lean_object* v_args_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_info_398_ = lean_ctor_get(v_n_396_, 0);
v_kind_399_ = lean_ctor_get(v_n_396_, 1);
v_args_400_ = lean_ctor_get(v_n_396_, 2);
v_isSharedCheck_408_ = !lean_is_exclusive(v_n_396_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v_n_396_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_args_400_);
lean_inc(v_kind_399_);
lean_inc(v_info_398_);
lean_dec(v_n_396_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_apply_1(v_fn_397_, v_args_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 2, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_info_398_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_kind_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
if (lean_obj_tag(v_x_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 1;
return v___x_411_;
}
else
{
uint8_t v___x_412_; 
v___x_412_ = 0;
return v___x_412_;
}
}
else
{
if (lean_obj_tag(v_x_410_) == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
else
{
lean_object* v_val_414_; lean_object* v_val_415_; uint8_t v___x_416_; 
v_val_414_ = lean_ctor_get(v_x_409_, 0);
v_val_415_ = lean_ctor_get(v_x_410_, 0);
v___x_416_ = l_Lean_Syntax_instBEqRange_beq(v_val_414_, v_val_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_417_, v_x_418_);
lean_dec(v_x_418_);
lean_dec(v_x_417_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
if (lean_obj_tag(v_x_422_) == 0)
{
uint8_t v___x_423_; 
v___x_423_ = 1;
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
else
{
if (lean_obj_tag(v_x_422_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v_tail_427_; lean_object* v_head_428_; lean_object* v_tail_429_; uint8_t v___x_430_; 
v_head_426_ = lean_ctor_get(v_x_421_, 0);
v_tail_427_ = lean_ctor_get(v_x_421_, 1);
v_head_428_ = lean_ctor_get(v_x_422_, 0);
v_tail_429_ = lean_ctor_get(v_x_422_, 1);
v___x_430_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_426_, v_head_428_);
if (v___x_430_ == 0)
{
return v___x_430_;
}
else
{
v_x_421_ = v_tail_427_;
v_x_422_ = v_tail_429_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_432_, v_x_433_);
lean_dec(v_x_433_);
lean_dec(v_x_432_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
switch(lean_obj_tag(v_x_436_))
{
case 0:
{
if (lean_obj_tag(v_x_437_) == 0)
{
uint8_t v___x_438_; 
v___x_438_ = 1;
return v___x_438_;
}
else
{
uint8_t v___x_439_; 
lean_dec(v_x_437_);
v___x_439_ = 0;
return v___x_439_;
}
}
case 1:
{
if (lean_obj_tag(v_x_437_) == 1)
{
lean_object* v_info_440_; lean_object* v_kind_441_; lean_object* v_args_442_; lean_object* v_info_443_; lean_object* v_kind_444_; lean_object* v_args_445_; uint8_t v___y_447_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_info_440_ = lean_ctor_get(v_x_436_, 0);
lean_inc(v_info_440_);
v_kind_441_ = lean_ctor_get(v_x_436_, 1);
lean_inc(v_kind_441_);
v_args_442_ = lean_ctor_get(v_x_436_, 2);
lean_inc_ref(v_args_442_);
lean_dec_ref_known(v_x_436_, 3);
v_info_443_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_info_443_);
v_kind_444_ = lean_ctor_get(v_x_437_, 1);
lean_inc(v_kind_444_);
v_args_445_ = lean_ctor_get(v_x_437_, 2);
lean_inc_ref(v_args_445_);
lean_dec_ref_known(v_x_437_, 3);
v___x_452_ = 0;
v___x_453_ = l_Lean_SourceInfo_getRange_x3f(v___x_452_, v_info_440_);
lean_dec(v_info_440_);
v___x_454_ = l_Lean_SourceInfo_getRange_x3f(v___x_452_, v_info_443_);
lean_dec(v_info_443_);
v___x_455_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_453_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_453_);
if (v___x_455_ == 0)
{
lean_dec(v_kind_444_);
lean_dec(v_kind_441_);
v___y_447_ = v___x_455_;
goto v___jp_446_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = lean_name_eq(v_kind_441_, v_kind_444_);
lean_dec(v_kind_444_);
lean_dec(v_kind_441_);
v___y_447_ = v___x_456_;
goto v___jp_446_;
}
v___jp_446_:
{
if (v___y_447_ == 0)
{
lean_dec_ref(v_args_445_);
lean_dec_ref(v_args_442_);
return v___y_447_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_array_get_size(v_args_442_);
v___x_449_ = lean_array_get_size(v_args_445_);
v___x_450_ = lean_nat_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec_ref(v_args_445_);
lean_dec_ref(v_args_442_);
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_args_442_, v_args_445_, v___x_448_);
lean_dec_ref(v_args_445_);
lean_dec_ref(v_args_442_);
return v___x_451_;
}
}
}
}
else
{
uint8_t v___x_457_; 
lean_dec_ref_known(v_x_436_, 3);
lean_dec(v_x_437_);
v___x_457_ = 0;
return v___x_457_;
}
}
case 2:
{
if (lean_obj_tag(v_x_437_) == 2)
{
lean_object* v_info_458_; lean_object* v_val_459_; lean_object* v_info_460_; lean_object* v_val_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_info_458_ = lean_ctor_get(v_x_436_, 0);
lean_inc(v_info_458_);
v_val_459_ = lean_ctor_get(v_x_436_, 1);
lean_inc_ref(v_val_459_);
lean_dec_ref_known(v_x_436_, 2);
v_info_460_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_info_460_);
v_val_461_ = lean_ctor_get(v_x_437_, 1);
lean_inc_ref(v_val_461_);
lean_dec_ref_known(v_x_437_, 2);
v___x_462_ = 0;
v___x_463_ = l_Lean_SourceInfo_getRange_x3f(v___x_462_, v_info_458_);
lean_dec(v_info_458_);
v___x_464_ = l_Lean_SourceInfo_getRange_x3f(v___x_462_, v_info_460_);
lean_dec(v_info_460_);
v___x_465_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_463_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_463_);
if (v___x_465_ == 0)
{
lean_dec_ref(v_val_461_);
lean_dec_ref(v_val_459_);
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = lean_string_dec_eq(v_val_459_, v_val_461_);
lean_dec_ref(v_val_461_);
lean_dec_ref(v_val_459_);
return v___x_466_;
}
}
else
{
uint8_t v___x_467_; 
lean_dec_ref_known(v_x_436_, 2);
lean_dec(v_x_437_);
v___x_467_ = 0;
return v___x_467_;
}
}
default: 
{
if (lean_obj_tag(v_x_437_) == 3)
{
lean_object* v_info_468_; lean_object* v_rawVal_469_; lean_object* v_val_470_; lean_object* v_preresolved_471_; lean_object* v_info_472_; lean_object* v_rawVal_473_; lean_object* v_val_474_; lean_object* v_preresolved_475_; uint8_t v___y_477_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_info_468_ = lean_ctor_get(v_x_436_, 0);
lean_inc(v_info_468_);
v_rawVal_469_ = lean_ctor_get(v_x_436_, 1);
lean_inc_ref(v_rawVal_469_);
v_val_470_ = lean_ctor_get(v_x_436_, 2);
lean_inc(v_val_470_);
v_preresolved_471_ = lean_ctor_get(v_x_436_, 3);
lean_inc(v_preresolved_471_);
lean_dec_ref_known(v_x_436_, 4);
v_info_472_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_info_472_);
v_rawVal_473_ = lean_ctor_get(v_x_437_, 1);
lean_inc_ref(v_rawVal_473_);
v_val_474_ = lean_ctor_get(v_x_437_, 2);
lean_inc(v_val_474_);
v_preresolved_475_ = lean_ctor_get(v_x_437_, 3);
lean_inc(v_preresolved_475_);
lean_dec_ref_known(v_x_437_, 4);
v___x_480_ = 0;
v___x_481_ = l_Lean_SourceInfo_getRange_x3f(v___x_480_, v_info_468_);
lean_dec(v_info_468_);
v___x_482_ = l_Lean_SourceInfo_getRange_x3f(v___x_480_, v_info_472_);
lean_dec(v_info_472_);
v___x_483_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_481_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_dec_ref(v_rawVal_473_);
lean_dec_ref(v_rawVal_469_);
v___y_477_ = v___x_483_;
goto v___jp_476_;
}
else
{
uint8_t v___x_484_; 
v___x_484_ = l_Substring_Raw_beq(v_rawVal_469_, v_rawVal_473_);
v___y_477_ = v___x_484_;
goto v___jp_476_;
}
v___jp_476_:
{
if (v___y_477_ == 0)
{
lean_dec(v_preresolved_475_);
lean_dec(v_val_474_);
lean_dec(v_preresolved_471_);
lean_dec(v_val_470_);
return v___y_477_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = lean_name_eq(v_val_470_, v_val_474_);
lean_dec(v_val_474_);
lean_dec(v_val_470_);
if (v___x_478_ == 0)
{
lean_dec(v_preresolved_475_);
lean_dec(v_preresolved_471_);
return v___x_478_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_471_, v_preresolved_475_);
lean_dec(v_preresolved_475_);
lean_dec(v_preresolved_471_);
return v___x_479_;
}
}
}
}
else
{
uint8_t v___x_485_; 
lean_dec_ref_known(v_x_436_, 4);
lean_dec(v_x_437_);
v___x_485_ = 0;
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object* v_xs_486_, lean_object* v_ys_487_, lean_object* v_x_488_){
_start:
{
lean_object* v_zero_489_; uint8_t v_isZero_490_; 
v_zero_489_ = lean_unsigned_to_nat(0u);
v_isZero_490_ = lean_nat_dec_eq(v_x_488_, v_zero_489_);
if (v_isZero_490_ == 1)
{
lean_dec(v_x_488_);
return v_isZero_490_;
}
else
{
lean_object* v_one_491_; lean_object* v_n_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_one_491_ = lean_unsigned_to_nat(1u);
v_n_492_ = lean_nat_sub(v_x_488_, v_one_491_);
lean_dec(v_x_488_);
v___x_493_ = lean_array_fget_borrowed(v_xs_486_, v_n_492_);
v___x_494_ = lean_array_fget_borrowed(v_ys_487_, v_n_492_);
lean_inc(v___x_494_);
lean_inc(v___x_493_);
v___x_495_ = l_Lean_Syntax_structRangeEq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v_n_492_);
return v___x_495_;
}
else
{
v_x_488_ = v_n_492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object* v_xs_497_, lean_object* v_ys_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_497_, v_ys_498_, v_x_499_);
lean_dec_ref(v_ys_498_);
lean_dec_ref(v_xs_497_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l_Lean_Syntax_structRangeEq(v_x_502_, v_x_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_xs_506_, lean_object* v_ys_507_, lean_object* v_hsz_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_506_, v_ys_507_, v_x_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_xs_512_, lean_object* v_ys_513_, lean_object* v_hsz_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_512_, v_ys_513_, v_hsz_514_, v_x_515_, v_x_516_);
lean_dec_ref(v_ys_513_);
lean_dec_ref(v_xs_512_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_519_, lean_object* v_x_520_){
_start:
{
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v___x_92__boxed_523_; uint8_t v_res_524_; lean_object* v_r_525_; 
v___x_92__boxed_523_ = lean_unbox(v___x_521_);
v_res_524_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_92__boxed_523_, v_x_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_535_, lean_object* v_stx1_536_, lean_object* v_stx2_537_){
_start:
{
uint8_t v___x_538_; uint8_t v___x_539_; 
lean_inc(v_stx2_537_);
lean_inc(v_stx1_536_);
v___x_538_ = l_Lean_Syntax_structRangeEq(v_stx1_536_, v_stx2_537_);
v___x_539_ = 1;
if (v___x_538_ == 0)
{
lean_object* v_map_540_; lean_object* v___x_541_; lean_object* v___f_542_; uint8_t v___y_544_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_map_540_ = lean_ctor_get(v_opts_535_, 0);
v___x_541_ = lean_box(v___x_538_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_542_, 0, v___x_541_);
v___x_559_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_560_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_540_, v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
v___y_544_ = v___x_538_;
goto v___jp_543_;
}
else
{
lean_object* v_val_561_; 
v_val_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v___x_560_, 1);
if (lean_obj_tag(v_val_561_) == 1)
{
uint8_t v_v_562_; 
v_v_562_ = lean_ctor_get_uint8(v_val_561_, 0);
lean_dec_ref_known(v_val_561_, 0);
v___y_544_ = v_v_562_;
goto v___jp_543_;
}
else
{
lean_dec(v_val_561_);
v___y_544_ = v___x_538_;
goto v___jp_543_;
}
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
lean_dec_ref(v___f_542_);
lean_dec(v_stx2_537_);
lean_dec(v_stx1_536_);
return v___x_538_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_545_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_546_ = lean_box(0);
v___x_547_ = l_Lean_Syntax_formatStx(v_stx1_536_, v___x_546_, v___x_539_);
v___x_548_ = l_Std_Format_defWidth;
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l_Std_Format_pretty(v___x_547_, v___x_548_, v___x_549_, v___x_549_);
v___x_551_ = lean_string_append(v___x_545_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
v___x_554_ = l_Lean_Syntax_formatStx(v_stx2_537_, v___x_546_, v___x_539_);
v___x_555_ = l_Std_Format_pretty(v___x_554_, v___x_548_, v___x_549_, v___x_549_);
v___x_556_ = lean_string_append(v___x_553_, v___x_555_);
lean_dec_ref(v___x_555_);
v___x_557_ = lean_dbg_trace(v___x_556_, v___f_542_);
v___x_558_ = lean_unbox(v___x_557_);
lean_dec(v___x_557_);
return v___x_558_;
}
}
}
else
{
lean_dec(v_stx2_537_);
lean_dec(v_stx1_536_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_563_, lean_object* v_stx1_564_, lean_object* v_stx2_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_563_, v_stx1_564_, v_stx2_565_);
lean_dec_ref(v_opts_563_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
switch(lean_obj_tag(v_x_568_))
{
case 0:
{
if (lean_obj_tag(v_x_569_) == 0)
{
uint8_t v___x_570_; 
v___x_570_ = 1;
return v___x_570_;
}
else
{
uint8_t v___x_571_; 
lean_dec(v_x_569_);
v___x_571_ = 0;
return v___x_571_;
}
}
case 1:
{
if (lean_obj_tag(v_x_569_) == 1)
{
lean_object* v_info_572_; lean_object* v_kind_573_; lean_object* v_args_574_; lean_object* v_info_575_; lean_object* v_kind_576_; lean_object* v_args_577_; uint8_t v___y_579_; uint8_t v___x_584_; 
v_info_572_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_info_572_);
v_kind_573_ = lean_ctor_get(v_x_568_, 1);
lean_inc(v_kind_573_);
v_args_574_ = lean_ctor_get(v_x_568_, 2);
lean_inc_ref(v_args_574_);
lean_dec_ref_known(v_x_568_, 3);
v_info_575_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_info_575_);
v_kind_576_ = lean_ctor_get(v_x_569_, 1);
lean_inc(v_kind_576_);
v_args_577_ = lean_ctor_get(v_x_569_, 2);
lean_inc_ref(v_args_577_);
lean_dec_ref_known(v_x_569_, 3);
v___x_584_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_572_, v_info_575_);
if (v___x_584_ == 0)
{
lean_dec(v_kind_576_);
lean_dec(v_kind_573_);
v___y_579_ = v___x_584_;
goto v___jp_578_;
}
else
{
uint8_t v___x_585_; 
v___x_585_ = lean_name_eq(v_kind_573_, v_kind_576_);
lean_dec(v_kind_576_);
lean_dec(v_kind_573_);
v___y_579_ = v___x_585_;
goto v___jp_578_;
}
v___jp_578_:
{
if (v___y_579_ == 0)
{
lean_dec_ref(v_args_577_);
lean_dec_ref(v_args_574_);
return v___y_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_array_get_size(v_args_574_);
v___x_581_ = lean_array_get_size(v_args_577_);
v___x_582_ = lean_nat_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_dec_ref(v_args_577_);
lean_dec_ref(v_args_574_);
return v___x_582_;
}
else
{
uint8_t v___x_583_; 
v___x_583_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_574_, v_args_577_, v___x_580_);
lean_dec_ref(v_args_577_);
lean_dec_ref(v_args_574_);
return v___x_583_;
}
}
}
}
else
{
uint8_t v___x_586_; 
lean_dec_ref_known(v_x_568_, 3);
lean_dec(v_x_569_);
v___x_586_ = 0;
return v___x_586_;
}
}
case 2:
{
if (lean_obj_tag(v_x_569_) == 2)
{
lean_object* v_info_587_; lean_object* v_val_588_; lean_object* v_info_589_; lean_object* v_val_590_; uint8_t v___x_591_; 
v_info_587_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_info_587_);
v_val_588_ = lean_ctor_get(v_x_568_, 1);
lean_inc_ref(v_val_588_);
lean_dec_ref_known(v_x_568_, 2);
v_info_589_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_info_589_);
v_val_590_ = lean_ctor_get(v_x_569_, 1);
lean_inc_ref(v_val_590_);
lean_dec_ref_known(v_x_569_, 2);
v___x_591_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_587_, v_info_589_);
if (v___x_591_ == 0)
{
lean_dec_ref(v_val_590_);
lean_dec_ref(v_val_588_);
return v___x_591_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = lean_string_dec_eq(v_val_588_, v_val_590_);
lean_dec_ref(v_val_590_);
lean_dec_ref(v_val_588_);
return v___x_592_;
}
}
else
{
uint8_t v___x_593_; 
lean_dec_ref_known(v_x_568_, 2);
lean_dec(v_x_569_);
v___x_593_ = 0;
return v___x_593_;
}
}
default: 
{
if (lean_obj_tag(v_x_569_) == 3)
{
lean_object* v_info_594_; lean_object* v_rawVal_595_; lean_object* v_val_596_; lean_object* v_preresolved_597_; lean_object* v_info_598_; lean_object* v_rawVal_599_; lean_object* v_val_600_; lean_object* v_preresolved_601_; uint8_t v___y_603_; uint8_t v___x_606_; 
v_info_594_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_info_594_);
v_rawVal_595_ = lean_ctor_get(v_x_568_, 1);
lean_inc_ref(v_rawVal_595_);
v_val_596_ = lean_ctor_get(v_x_568_, 2);
lean_inc(v_val_596_);
v_preresolved_597_ = lean_ctor_get(v_x_568_, 3);
lean_inc(v_preresolved_597_);
lean_dec_ref_known(v_x_568_, 4);
v_info_598_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_info_598_);
v_rawVal_599_ = lean_ctor_get(v_x_569_, 1);
lean_inc_ref(v_rawVal_599_);
v_val_600_ = lean_ctor_get(v_x_569_, 2);
lean_inc(v_val_600_);
v_preresolved_601_ = lean_ctor_get(v_x_569_, 3);
lean_inc(v_preresolved_601_);
lean_dec_ref_known(v_x_569_, 4);
v___x_606_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_594_, v_info_598_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_rawVal_599_);
lean_dec_ref(v_rawVal_595_);
v___y_603_ = v___x_606_;
goto v___jp_602_;
}
else
{
uint8_t v___x_607_; 
v___x_607_ = l_Substring_Raw_beq(v_rawVal_595_, v_rawVal_599_);
v___y_603_ = v___x_607_;
goto v___jp_602_;
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
lean_dec(v_preresolved_601_);
lean_dec(v_val_600_);
lean_dec(v_preresolved_597_);
lean_dec(v_val_596_);
return v___y_603_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = lean_name_eq(v_val_596_, v_val_600_);
lean_dec(v_val_600_);
lean_dec(v_val_596_);
if (v___x_604_ == 0)
{
lean_dec(v_preresolved_601_);
lean_dec(v_preresolved_597_);
return v___x_604_;
}
else
{
uint8_t v___x_605_; 
v___x_605_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_597_, v_preresolved_601_);
lean_dec(v_preresolved_601_);
lean_dec(v_preresolved_597_);
return v___x_605_;
}
}
}
}
else
{
uint8_t v___x_608_; 
lean_dec_ref_known(v_x_568_, 4);
lean_dec(v_x_569_);
v___x_608_ = 0;
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_609_, lean_object* v_ys_610_, lean_object* v_x_611_){
_start:
{
lean_object* v_zero_612_; uint8_t v_isZero_613_; 
v_zero_612_ = lean_unsigned_to_nat(0u);
v_isZero_613_ = lean_nat_dec_eq(v_x_611_, v_zero_612_);
if (v_isZero_613_ == 1)
{
lean_dec(v_x_611_);
return v_isZero_613_;
}
else
{
lean_object* v_one_614_; lean_object* v_n_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_one_614_ = lean_unsigned_to_nat(1u);
v_n_615_ = lean_nat_sub(v_x_611_, v_one_614_);
lean_dec(v_x_611_);
v___x_616_ = lean_array_fget_borrowed(v_xs_609_, v_n_615_);
v___x_617_ = lean_array_fget_borrowed(v_ys_610_, v_n_615_);
lean_inc(v___x_617_);
lean_inc(v___x_616_);
v___x_618_ = l_Lean_Syntax_eqWithInfo(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_n_615_);
return v___x_618_;
}
else
{
v_x_611_ = v_n_615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_620_, lean_object* v_ys_621_, lean_object* v_x_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_620_, v_ys_621_, v_x_622_);
lean_dec_ref(v_ys_621_);
lean_dec_ref(v_xs_620_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Lean_Syntax_eqWithInfo(v_x_625_, v_x_626_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_629_, lean_object* v_ys_630_, lean_object* v_hsz_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_629_, v_ys_630_, v_x_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_635_, lean_object* v_ys_636_, lean_object* v_hsz_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_635_, v_ys_636_, v_hsz_637_, v_x_638_, v_x_639_);
lean_dec_ref(v_ys_636_);
lean_dec_ref(v_xs_635_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_642_, lean_object* v_stx1_643_, lean_object* v_stx2_644_){
_start:
{
uint8_t v___x_645_; uint8_t v___x_646_; 
lean_inc(v_stx2_644_);
lean_inc(v_stx1_643_);
v___x_645_ = l_Lean_Syntax_eqWithInfo(v_stx1_643_, v_stx2_644_);
v___x_646_ = 1;
if (v___x_645_ == 0)
{
lean_object* v_map_647_; lean_object* v___x_648_; lean_object* v___f_649_; uint8_t v___y_651_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_map_647_ = lean_ctor_get(v_opts_642_, 0);
v___x_648_ = lean_box(v___x_645_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_649_, 0, v___x_648_);
v___x_666_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_647_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
v___y_651_ = v___x_645_;
goto v___jp_650_;
}
else
{
lean_object* v_val_668_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
if (lean_obj_tag(v_val_668_) == 1)
{
uint8_t v_v_669_; 
v_v_669_ = lean_ctor_get_uint8(v_val_668_, 0);
lean_dec_ref_known(v_val_668_, 0);
v___y_651_ = v_v_669_;
goto v___jp_650_;
}
else
{
lean_dec(v_val_668_);
v___y_651_ = v___x_645_;
goto v___jp_650_;
}
}
v___jp_650_:
{
if (v___y_651_ == 0)
{
lean_dec_ref(v___f_649_);
lean_dec(v_stx2_644_);
lean_dec(v_stx1_643_);
return v___x_645_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_652_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_653_ = lean_box(0);
v___x_654_ = l_Lean_Syntax_formatStx(v_stx1_643_, v___x_653_, v___x_646_);
v___x_655_ = l_Std_Format_defWidth;
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Std_Format_pretty(v___x_654_, v___x_655_, v___x_656_, v___x_656_);
v___x_658_ = lean_string_append(v___x_652_, v___x_657_);
lean_dec_ref(v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_660_ = lean_string_append(v___x_658_, v___x_659_);
v___x_661_ = l_Lean_Syntax_formatStx(v_stx2_644_, v___x_653_, v___x_646_);
v___x_662_ = l_Std_Format_pretty(v___x_661_, v___x_655_, v___x_656_, v___x_656_);
v___x_663_ = lean_string_append(v___x_660_, v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_dbg_trace(v___x_663_, v___f_649_);
v___x_665_ = lean_unbox(v___x_664_);
lean_dec(v___x_664_);
return v___x_665_;
}
}
}
else
{
lean_dec(v_stx2_644_);
lean_dec(v_stx1_643_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_670_, lean_object* v_stx1_671_, lean_object* v_stx2_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_670_, v_stx1_671_, v_stx2_672_);
lean_dec_ref(v_opts_670_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 2)
{
lean_object* v_val_677_; 
v_val_677_ = lean_ctor_get(v_x_676_, 1);
lean_inc_ref(v_val_677_);
return v_val_677_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Syntax_getAtomVal(v_x_679_);
lean_dec(v_x_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_681_) == 2)
{
lean_object* v_info_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_info_683_ = lean_ctor_get(v_x_681_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v_x_681_, 1);
lean_dec(v_unused_691_);
v___x_685_ = v_x_681_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_info_683_);
lean_dec(v_x_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_x_682_);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_info_683_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_x_682_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
lean_dec_ref(v_x_682_);
return v_x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_692_, lean_object* v_hyes_693_, lean_object* v_hno_694_){
_start:
{
if (lean_obj_tag(v_stx_692_) == 1)
{
lean_object* v___x_695_; 
lean_dec(v_hno_694_);
v___x_695_ = lean_apply_1(v_hyes_693_, v_stx_692_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_hyes_693_);
lean_dec(v_stx_692_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_apply_1(v_hno_694_, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_698_, lean_object* v_stx_699_, lean_object* v_hyes_700_, lean_object* v_hno_701_){
_start:
{
if (lean_obj_tag(v_stx_699_) == 1)
{
lean_object* v___x_702_; 
lean_dec(v_hno_701_);
v___x_702_ = lean_apply_1(v_hyes_700_, v_stx_699_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_hyes_700_);
lean_dec(v_stx_699_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_apply_1(v_hno_701_, v___x_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_705_, lean_object* v_kind_706_, lean_object* v_hyes_707_, lean_object* v_hno_708_){
_start:
{
if (lean_obj_tag(v_stx_705_) == 1)
{
lean_object* v_kind_709_; uint8_t v___x_710_; 
v_kind_709_ = lean_ctor_get(v_stx_705_, 1);
v___x_710_ = lean_name_eq(v_kind_709_, v_kind_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec_ref_known(v_stx_705_, 3);
lean_dec(v_hyes_707_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_apply_1(v_hno_708_, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
lean_dec(v_hno_708_);
v___x_713_ = lean_apply_1(v_hyes_707_, v_stx_705_);
return v___x_713_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_hyes_707_);
lean_dec(v_stx_705_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_apply_1(v_hno_708_, v___x_714_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_716_, lean_object* v_kind_717_, lean_object* v_hyes_718_, lean_object* v_hno_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_716_, v_kind_717_, v_hyes_718_, v_hno_719_);
lean_dec(v_kind_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_721_, lean_object* v_stx_722_, lean_object* v_kind_723_, lean_object* v_hyes_724_, lean_object* v_hno_725_){
_start:
{
if (lean_obj_tag(v_stx_722_) == 1)
{
lean_object* v_kind_726_; uint8_t v___x_727_; 
v_kind_726_ = lean_ctor_get(v_stx_722_, 1);
v___x_727_ = lean_name_eq(v_kind_726_, v_kind_723_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref_known(v_stx_722_, 3);
lean_dec(v_hyes_724_);
v___x_728_ = lean_box(0);
v___x_729_ = lean_apply_1(v_hno_725_, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; 
lean_dec(v_hno_725_);
v___x_730_ = lean_apply_1(v_hyes_724_, v_stx_722_);
return v___x_730_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v_hyes_724_);
lean_dec(v_stx_722_);
v___x_731_ = lean_box(0);
v___x_732_ = lean_apply_1(v_hno_725_, v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_733_, lean_object* v_stx_734_, lean_object* v_kind_735_, lean_object* v_hyes_736_, lean_object* v_hno_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_733_, v_stx_734_, v_kind_735_, v_hyes_736_, v_hno_737_);
lean_dec(v_kind_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 1)
{
lean_inc_ref(v_x_748_);
return v_x_748_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Syntax_asNode(v_x_750_);
lean_dec(v_x_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_752_, lean_object* v_i_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l_Lean_Syntax_getArg(v_stx_752_, v_i_753_);
v___x_755_ = l_Lean_Syntax_getId(v___x_754_);
lean_dec(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_756_, lean_object* v_i_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Syntax_getIdAt(v_stx_756_, v_i_757_);
lean_dec(v_i_757_);
lean_dec(v_stx_756_);
return v_res_758_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_759_, lean_object* v_x_760_){
_start:
{
switch(lean_obj_tag(v_x_760_))
{
case 3:
{
lean_object* v_val_761_; uint8_t v___x_762_; 
v_val_761_ = lean_ctor_get(v_x_760_, 2);
v___x_762_ = lean_name_eq(v_id_759_, v_val_761_);
return v___x_762_;
}
case 1:
{
lean_object* v_args_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_args_763_ = lean_ctor_get(v_x_760_, 2);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_args_763_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
return v___x_766_;
}
else
{
if (v___x_766_ == 0)
{
return v___x_766_;
}
else
{
size_t v___x_767_; size_t v___x_768_; uint8_t v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_of_nat(v___x_765_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_759_, v_args_763_, v___x_767_, v___x_768_);
return v___x_769_;
}
}
}
default: 
{
uint8_t v___x_770_; 
v___x_770_ = 0;
return v___x_770_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_771_, lean_object* v_as_772_, size_t v_i_773_, size_t v_stop_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_773_, v_stop_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = lean_array_uget_borrowed(v_as_772_, v_i_773_);
v___x_777_ = l_Lean_Syntax_hasIdent(v_id_771_, v___x_776_);
if (v___x_777_ == 0)
{
size_t v___x_778_; size_t v___x_779_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_773_, v___x_778_);
v_i_773_ = v___x_779_;
goto _start;
}
else
{
return v___x_777_;
}
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_782_, lean_object* v_as_783_, lean_object* v_i_784_, lean_object* v_stop_785_){
_start:
{
size_t v_i_boxed_786_; size_t v_stop_boxed_787_; uint8_t v_res_788_; lean_object* v_r_789_; 
v_i_boxed_786_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_stop_boxed_787_ = lean_unbox_usize(v_stop_785_);
lean_dec(v_stop_785_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_782_, v_as_783_, v_i_boxed_786_, v_stop_boxed_787_);
lean_dec_ref(v_as_783_);
lean_dec(v_id_782_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_790_, lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Lean_Syntax_hasIdent(v_id_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec(v_id_790_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_794_, lean_object* v_fn_795_){
_start:
{
if (lean_obj_tag(v_stx_794_) == 1)
{
lean_object* v_info_796_; lean_object* v_kind_797_; lean_object* v_args_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_info_796_ = lean_ctor_get(v_stx_794_, 0);
v_kind_797_ = lean_ctor_get(v_stx_794_, 1);
v_args_798_ = lean_ctor_get(v_stx_794_, 2);
v_isSharedCheck_806_ = !lean_is_exclusive(v_stx_794_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v_stx_794_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_args_798_);
lean_inc(v_kind_797_);
lean_inc(v_info_796_);
lean_dec(v_stx_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_apply_1(v_fn_795_, v_args_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 2, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_info_796_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_kind_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_dec_ref(v_fn_795_);
return v_stx_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_807_, lean_object* v_i_808_, lean_object* v_fn_809_){
_start:
{
if (lean_obj_tag(v_stx_807_) == 1)
{
lean_object* v_info_810_; lean_object* v_kind_811_; lean_object* v_args_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_info_810_ = lean_ctor_get(v_stx_807_, 0);
v_kind_811_ = lean_ctor_get(v_stx_807_, 1);
v_args_812_ = lean_ctor_get(v_stx_807_, 2);
v___x_813_ = lean_array_get_size(v_args_812_);
v___x_814_ = lean_nat_dec_lt(v_i_808_, v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v_fn_809_);
return v_stx_807_;
}
else
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_826_; 
lean_inc_ref(v_args_812_);
lean_inc(v_kind_811_);
lean_inc(v_info_810_);
v_isSharedCheck_826_ = !lean_is_exclusive(v_stx_807_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; lean_object* v_unused_828_; lean_object* v_unused_829_; 
v_unused_827_ = lean_ctor_get(v_stx_807_, 2);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_stx_807_, 1);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_stx_807_, 0);
lean_dec(v_unused_829_);
v___x_816_ = v_stx_807_;
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_stx_807_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_v_818_; lean_object* v___x_819_; lean_object* v_xs_x27_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v_v_818_ = lean_array_fget(v_args_812_, v_i_808_);
v___x_819_ = lean_box(0);
v_xs_x27_820_ = lean_array_fset(v_args_812_, v_i_808_, v___x_819_);
v___x_821_ = lean_apply_1(v_fn_809_, v_v_818_);
v___x_822_ = lean_array_fset(v_xs_x27_820_, v_i_808_, v___x_821_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 2, v___x_822_);
v___x_824_ = v___x_816_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_info_810_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_kind_811_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_dec_ref(v_fn_809_);
return v_stx_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_830_, lean_object* v_i_831_, lean_object* v_fn_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Syntax_modifyArg(v_stx_830_, v_i_831_, v_fn_832_);
lean_dec(v_i_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_834_, lean_object* v_kind_835_, lean_object* v_toPure_836_, lean_object* v_____do__lift_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_838_, 0, v_info_834_);
lean_ctor_set(v___x_838_, 1, v_kind_835_);
lean_ctor_set(v___x_838_, 2, v_____do__lift_837_);
v___x_839_ = lean_apply_2(v_toPure_836_, lean_box(0), v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_840_, lean_object* v_x_841_, lean_object* v_o_842_){
_start:
{
if (lean_obj_tag(v_o_842_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_2(v_toPure_840_, lean_box(0), v_x_841_);
return v___x_843_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_845_; 
lean_dec(v_x_841_);
v_val_844_ = lean_ctor_get(v_o_842_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v_o_842_, 1);
v___x_845_ = lean_apply_2(v_toPure_840_, lean_box(0), v_val_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_846_, lean_object* v_fn_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 1)
{
lean_object* v_toApplicative_849_; lean_object* v_toBind_850_; lean_object* v_toPure_851_; lean_object* v_info_852_; lean_object* v_kind_853_; lean_object* v_args_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_toApplicative_849_ = lean_ctor_get(v_inst_846_, 0);
v_toBind_850_ = lean_ctor_get(v_inst_846_, 1);
lean_inc_n(v_toBind_850_, 2);
v_toPure_851_ = lean_ctor_get(v_toApplicative_849_, 1);
lean_inc_n(v_toPure_851_, 2);
v_info_852_ = lean_ctor_get(v_x_848_, 0);
v_kind_853_ = lean_ctor_get(v_x_848_, 1);
v_args_854_ = lean_ctor_get(v_x_848_, 2);
lean_inc(v_kind_853_);
lean_inc(v_info_852_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_855_, 0, v_info_852_);
lean_closure_set(v___f_855_, 1, v_kind_853_);
lean_closure_set(v___f_855_, 2, v_toPure_851_);
lean_inc_ref(v_args_854_);
lean_inc(v_fn_847_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_856_, 0, v_inst_846_);
lean_closure_set(v___f_856_, 1, v_fn_847_);
lean_closure_set(v___f_856_, 2, v_args_854_);
lean_closure_set(v___f_856_, 3, v_toBind_850_);
lean_closure_set(v___f_856_, 4, v___f_855_);
lean_closure_set(v___f_856_, 5, v_toPure_851_);
v___x_857_ = lean_apply_1(v_fn_847_, v_x_848_);
v___x_858_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v___x_857_, v___f_856_);
return v___x_858_;
}
else
{
lean_object* v_toApplicative_859_; lean_object* v_toBind_860_; lean_object* v_toPure_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_toApplicative_859_ = lean_ctor_get(v_inst_846_, 0);
lean_inc_ref(v_toApplicative_859_);
v_toBind_860_ = lean_ctor_get(v_inst_846_, 1);
lean_inc(v_toBind_860_);
lean_dec_ref(v_inst_846_);
v_toPure_861_ = lean_ctor_get(v_toApplicative_859_, 1);
lean_inc(v_toPure_861_);
lean_dec_ref(v_toApplicative_859_);
lean_inc(v_x_848_);
v___f_862_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_862_, 0, v_toPure_861_);
lean_closure_set(v___f_862_, 1, v_x_848_);
v___x_863_ = lean_apply_1(v_fn_847_, v_x_848_);
v___x_864_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_863_, v___f_862_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_865_, lean_object* v_fn_866_, lean_object* v_args_867_, lean_object* v_toBind_868_, lean_object* v___f_869_, lean_object* v_toPure_870_, lean_object* v_____do__lift_871_){
_start:
{
if (lean_obj_tag(v_____do__lift_871_) == 0)
{
lean_object* v___x_872_; size_t v_sz_873_; size_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v_toPure_870_);
lean_inc_ref(v_inst_865_);
v___x_872_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_872_, 0, v_inst_865_);
lean_closure_set(v___x_872_, 1, v_fn_866_);
v_sz_873_ = lean_array_size(v_args_867_);
v___x_874_ = ((size_t)0ULL);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_865_, v___x_872_, v_sz_873_, v___x_874_, v_args_867_);
v___x_876_ = lean_apply_4(v_toBind_868_, lean_box(0), lean_box(0), v___x_875_, v___f_869_);
return v___x_876_;
}
else
{
lean_object* v_val_877_; lean_object* v___x_878_; 
lean_dec(v___f_869_);
lean_dec(v_toBind_868_);
lean_dec_ref(v_args_867_);
lean_dec(v_fn_866_);
lean_dec_ref(v_inst_865_);
v_val_877_ = lean_ctor_get(v_____do__lift_871_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v_____do__lift_871_, 1);
v___x_878_ = lean_apply_2(v_toPure_870_, lean_box(0), v_val_877_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_879_, lean_object* v_inst_880_, lean_object* v_fn_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Syntax_replaceM___redArg(v_inst_880_, v_fn_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_884_, lean_object* v_kind_885_, lean_object* v_fn_886_, lean_object* v_args_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_888_, 0, v_info_884_);
lean_ctor_set(v___x_888_, 1, v_kind_885_);
lean_ctor_set(v___x_888_, 2, v_args_887_);
v___x_889_ = lean_apply_1(v_fn_886_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_890_, lean_object* v_fn_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 1)
{
lean_object* v_toBind_893_; lean_object* v_info_894_; lean_object* v_kind_895_; lean_object* v_args_896_; lean_object* v___f_897_; lean_object* v___x_898_; size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toBind_893_ = lean_ctor_get(v_inst_890_, 1);
lean_inc(v_toBind_893_);
v_info_894_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_info_894_);
v_kind_895_ = lean_ctor_get(v_x_892_, 1);
lean_inc(v_kind_895_);
v_args_896_ = lean_ctor_get(v_x_892_, 2);
lean_inc_ref(v_args_896_);
lean_dec_ref_known(v_x_892_, 3);
lean_inc(v_fn_891_);
v___f_897_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_897_, 0, v_info_894_);
lean_closure_set(v___f_897_, 1, v_kind_895_);
lean_closure_set(v___f_897_, 2, v_fn_891_);
lean_inc_ref(v_inst_890_);
v___x_898_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_898_, 0, v_inst_890_);
lean_closure_set(v___x_898_, 1, v_fn_891_);
v_sz_899_ = lean_array_size(v_args_896_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_890_, v___x_898_, v_sz_899_, v___x_900_, v_args_896_);
v___x_902_ = lean_apply_4(v_toBind_893_, lean_box(0), lean_box(0), v___x_901_, v___f_897_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v_inst_890_);
v___x_903_ = lean_apply_1(v_fn_891_, v_x_892_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_904_, lean_object* v_inst_905_, lean_object* v_fn_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_905_, v_fn_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_apply_1(v_fn_909_, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_931_, lean_object* v_stx_932_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___f_933_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_933_, 0, v_fn_931_);
v___x_934_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_935_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_934_, v___f_933_, v_stx_932_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_936_) == 0)
{
lean_object* v_leading_939_; lean_object* v_trailing_940_; lean_object* v_pos_941_; lean_object* v_endPos_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_969_; 
v_leading_939_ = lean_ctor_get(v_x_936_, 0);
v_trailing_940_ = lean_ctor_get(v_x_936_, 2);
v_pos_941_ = lean_ctor_get(v_x_936_, 1);
v_endPos_942_ = lean_ctor_get(v_x_936_, 3);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_936_);
if (v_isSharedCheck_969_ == 0)
{
v___x_944_ = v_x_936_;
v_isShared_945_ = v_isSharedCheck_969_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_endPos_942_);
lean_inc(v_trailing_940_);
lean_inc(v_pos_941_);
lean_inc(v_leading_939_);
lean_dec(v_x_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_969_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_str_946_; lean_object* v_stopPos_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_967_; 
v_str_946_ = lean_ctor_get(v_leading_939_, 0);
v_stopPos_947_ = lean_ctor_get(v_leading_939_, 2);
v_isSharedCheck_967_ = !lean_is_exclusive(v_leading_939_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_leading_939_, 1);
lean_dec(v_unused_968_);
v___x_949_ = v_leading_939_;
v_isShared_950_ = v_isSharedCheck_967_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_stopPos_947_);
lean_inc(v_str_946_);
lean_dec(v_leading_939_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_967_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_str_951_; lean_object* v_startPos_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_965_; 
v_str_951_ = lean_ctor_get(v_trailing_940_, 0);
v_startPos_952_ = lean_ctor_get(v_trailing_940_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_trailing_940_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_trailing_940_, 2);
lean_dec(v_unused_966_);
v___x_954_ = v_trailing_940_;
v_isShared_955_ = v_isSharedCheck_965_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_startPos_952_);
lean_inc(v_str_951_);
lean_dec(v_trailing_940_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_965_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 2, v_stopPos_947_);
lean_ctor_set(v___x_954_, 1, v_x_937_);
lean_ctor_set(v___x_954_, 0, v_str_946_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_str_946_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_x_937_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_stopPos_947_);
v___x_957_ = v_reuseFailAlloc_964_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_959_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v_x_938_);
lean_ctor_set(v___x_949_, 1, v_startPos_952_);
lean_ctor_set(v___x_949_, 0, v_str_951_);
v___x_959_ = v___x_949_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_str_951_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_startPos_952_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_x_938_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v___x_959_);
lean_ctor_set(v___x_944_, 0, v___x_957_);
v___x_961_ = v___x_944_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_pos_941_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_endPos_942_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_938_);
lean_dec(v_x_937_);
return v_x_936_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v_a_973_, lean_object* v_b_974_){
_start:
{
lean_object* v___x_975_; uint8_t v_decide_976_; 
v___x_975_ = lean_nat_sub(v___x_970_, v___x_971_);
v_decide_976_ = lean_nat_dec_eq(v_a_973_, v___x_975_);
lean_dec(v___x_975_);
if (v_decide_976_ == 0)
{
uint32_t v___x_977_; lean_object* v___x_978_; uint32_t v___x_979_; uint8_t v___x_980_; 
v___x_977_ = 10;
v___x_978_ = lean_nat_add(v___x_971_, v_a_973_);
v___x_979_ = lean_string_utf8_get_fast(v___x_972_, v___x_978_);
v___x_980_ = lean_uint32_dec_eq(v___x_979_, v___x_977_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_a_973_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_string_utf8_next_fast(v___x_972_, v___x_978_);
lean_dec(v___x_978_);
v___x_983_ = lean_nat_sub(v___x_982_, v___x_971_);
v_a_973_ = v___x_983_;
v_b_974_ = v___x_981_;
goto _start;
}
else
{
lean_object* v___x_985_; 
lean_dec(v___x_978_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_a_973_);
return v___x_985_;
}
}
else
{
lean_dec(v_a_973_);
lean_inc(v_b_974_);
return v_b_974_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v_a_989_, lean_object* v_b_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_986_, v___x_987_, v___x_988_, v_a_989_, v_b_990_);
lean_dec(v_b_990_);
lean_dec_ref(v___x_988_);
lean_dec(v___x_987_);
lean_dec(v___x_986_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_992_){
_start:
{
lean_object* v_str_993_; lean_object* v_startPos_994_; lean_object* v_stopPos_995_; uint8_t v___y_997_; uint8_t v___x_1007_; uint8_t v___y_1009_; uint8_t v___x_1010_; 
v_str_993_ = lean_ctor_get(v_trail_992_, 0);
v_startPos_994_ = lean_ctor_get(v_trail_992_, 1);
v_stopPos_995_ = lean_ctor_get(v_trail_992_, 2);
v___x_1007_ = lean_string_is_valid_pos(v_str_993_, v_startPos_994_);
v___x_1010_ = lean_string_is_valid_pos(v_str_993_, v_stopPos_995_);
if (v___x_1010_ == 0)
{
v___y_1009_ = v___x_1010_;
goto v___jp_1008_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_nat_dec_le(v_startPos_994_, v_stopPos_995_);
v___y_1009_ = v___x_1011_;
goto v___jp_1008_;
}
v___jp_996_:
{
if (v___y_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_nat_sub(v_stopPos_995_, v_startPos_994_);
v___x_999_ = lean_nat_add(v_startPos_994_, v___x_998_);
lean_dec(v___x_998_);
return v___x_999_;
}
else
{
lean_object* v_searcher_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_searcher_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_box(0);
v___x_1002_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v_stopPos_995_, v_startPos_994_, v_str_993_, v_searcher_1000_, v___x_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_nat_sub(v_stopPos_995_, v_startPos_994_);
v___x_1004_ = lean_nat_add(v_startPos_994_, v___x_1003_);
lean_dec(v___x_1003_);
return v___x_1004_;
}
else
{
lean_object* v_val_1005_; lean_object* v___x_1006_; 
v_val_1005_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1006_ = lean_nat_add(v_startPos_994_, v_val_1005_);
lean_dec(v_val_1005_);
return v___x_1006_;
}
}
}
v___jp_1008_:
{
if (v___x_1007_ == 0)
{
v___y_997_ = v___x_1007_;
goto v___jp_996_;
}
else
{
v___y_997_ = v___y_1009_;
goto v___jp_996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object* v_trail_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trail_1012_);
lean_dec_ref(v_trail_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v___x_1016_, lean_object* v___x_1017_, lean_object* v_inst_1018_, lean_object* v_R_1019_, lean_object* v_a_1020_, lean_object* v_b_1021_, lean_object* v_c_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1014_, v___x_1015_, v___x_1017_, v_a_1020_, v_b_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_inst_1028_, lean_object* v_R_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v_c_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1024_, v___x_1025_, v___x_1026_, v___x_1027_, v_inst_1028_, v_R_1029_, v_a_1030_, v_b_1031_, v_c_1032_);
lean_dec(v_b_1031_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v___x_1025_);
lean_dec(v___x_1024_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___y_1037_; 
switch(lean_obj_tag(v_x_1034_))
{
case 2:
{
lean_object* v_info_1040_; 
v_info_1040_ = lean_ctor_get(v_x_1034_, 0);
lean_inc(v_info_1040_);
if (lean_obj_tag(v_info_1040_) == 0)
{
lean_object* v_val_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1053_; 
v_val_1041_ = lean_ctor_get(v_x_1034_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1054_);
v___x_1043_ = v_x_1034_;
v_isShared_1044_ = v_isSharedCheck_1053_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_val_1041_);
lean_dec(v_x_1034_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1053_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_trailing_1045_; lean_object* v_trailStop_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v_trailing_1045_ = lean_ctor_get(v_info_1040_, 2);
v_trailStop_1046_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1045_);
lean_inc(v_trailStop_1046_);
v___x_1047_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1040_, v_a_1035_, v_trailStop_1046_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1047_);
v___x_1049_ = v___x_1043_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_val_1041_);
v___x_1049_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_trailStop_1046_);
return v___x_1051_;
}
}
}
else
{
lean_dec_ref_known(v_x_1034_, 2);
lean_dec(v_info_1040_);
v___y_1037_ = v_a_1035_;
goto v___jp_1036_;
}
}
case 3:
{
lean_object* v_info_1055_; 
v_info_1055_ = lean_ctor_get(v_x_1034_, 0);
lean_inc(v_info_1055_);
if (lean_obj_tag(v_info_1055_) == 0)
{
lean_object* v_rawVal_1056_; lean_object* v_val_1057_; lean_object* v_preresolved_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1070_; 
v_rawVal_1056_ = lean_ctor_get(v_x_1034_, 1);
v_val_1057_ = lean_ctor_get(v_x_1034_, 2);
v_preresolved_1058_ = lean_ctor_get(v_x_1034_, 3);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1071_);
v___x_1060_ = v_x_1034_;
v_isShared_1061_ = v_isSharedCheck_1070_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_preresolved_1058_);
lean_inc(v_val_1057_);
lean_inc(v_rawVal_1056_);
lean_dec(v_x_1034_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1070_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_trailing_1062_; lean_object* v_trailStop_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v_trailing_1062_ = lean_ctor_get(v_info_1055_, 2);
v_trailStop_1063_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1062_);
lean_inc(v_trailStop_1063_);
v___x_1064_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1055_, v_a_1035_, v_trailStop_1063_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1064_);
v___x_1066_ = v___x_1060_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_rawVal_1056_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_val_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_preresolved_1058_);
v___x_1066_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v_trailStop_1063_);
return v___x_1068_;
}
}
}
else
{
lean_dec_ref_known(v_x_1034_, 4);
lean_dec(v_info_1055_);
v___y_1037_ = v_a_1035_;
goto v___jp_1036_;
}
}
default: 
{
lean_dec(v_x_1034_);
v___y_1037_ = v_a_1035_;
goto v___jp_1036_;
}
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___y_1037_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
switch(lean_obj_tag(v___y_1072_))
{
case 2:
{
lean_object* v_info_1077_; 
v_info_1077_ = lean_ctor_get(v___y_1072_, 0);
lean_inc(v_info_1077_);
if (lean_obj_tag(v_info_1077_) == 0)
{
lean_object* v_val_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1090_; 
v_val_1078_ = lean_ctor_get(v___y_1072_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___y_1072_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___y_1072_, 0);
lean_dec(v_unused_1091_);
v___x_1080_ = v___y_1072_;
v_isShared_1081_ = v_isSharedCheck_1090_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_val_1078_);
lean_dec(v___y_1072_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1090_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_trailing_1082_; lean_object* v_trailStop_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v_trailing_1082_ = lean_ctor_get(v_info_1077_, 2);
v_trailStop_1083_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1082_);
lean_inc(v_trailStop_1083_);
v___x_1084_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1077_, v___y_1073_, v_trailStop_1083_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1084_);
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_val_1078_);
v___x_1086_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_trailStop_1083_);
return v___x_1088_;
}
}
}
else
{
lean_dec(v_info_1077_);
lean_dec_ref_known(v___y_1072_, 2);
goto v___jp_1074_;
}
}
case 3:
{
lean_object* v_info_1092_; 
v_info_1092_ = lean_ctor_get(v___y_1072_, 0);
lean_inc(v_info_1092_);
if (lean_obj_tag(v_info_1092_) == 0)
{
lean_object* v_rawVal_1093_; lean_object* v_val_1094_; lean_object* v_preresolved_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1107_; 
v_rawVal_1093_ = lean_ctor_get(v___y_1072_, 1);
v_val_1094_ = lean_ctor_get(v___y_1072_, 2);
v_preresolved_1095_ = lean_ctor_get(v___y_1072_, 3);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1072_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___y_1072_, 0);
lean_dec(v_unused_1108_);
v___x_1097_ = v___y_1072_;
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_preresolved_1095_);
lean_inc(v_val_1094_);
lean_inc(v_rawVal_1093_);
lean_dec(v___y_1072_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_trailing_1099_; lean_object* v_trailStop_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v_trailing_1099_ = lean_ctor_get(v_info_1092_, 2);
v_trailStop_1100_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1099_);
lean_inc(v_trailStop_1100_);
v___x_1101_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1092_, v___y_1073_, v_trailStop_1100_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1101_);
v___x_1103_ = v___x_1097_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_rawVal_1093_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_val_1094_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_preresolved_1095_);
v___x_1103_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_trailStop_1100_);
return v___x_1105_;
}
}
}
else
{
lean_dec_ref_known(v___y_1072_, 4);
lean_dec(v_info_1092_);
goto v___jp_1074_;
}
}
default: 
{
lean_dec(v___y_1072_);
goto v___jp_1074_;
}
}
v___jp_1074_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___y_1073_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1109_, lean_object* v___y_1110_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 1)
{
lean_object* v_info_1111_; lean_object* v_kind_1112_; lean_object* v_args_1113_; lean_object* v___x_1114_; lean_object* v_fst_1115_; 
v_info_1111_ = lean_ctor_get(v_x_1109_, 0);
lean_inc(v_info_1111_);
v_kind_1112_ = lean_ctor_get(v_x_1109_, 1);
lean_inc(v_kind_1112_);
v_args_1113_ = lean_ctor_get(v_x_1109_, 2);
lean_inc_ref(v_args_1113_);
v___x_1114_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1109_, v___y_1110_);
v_fst_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_fst_1115_);
if (lean_obj_tag(v_fst_1115_) == 0)
{
lean_object* v_snd_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_snd_1116_ = lean_ctor_get(v___x_1114_, 1);
lean_inc(v_snd_1116_);
lean_dec_ref(v___x_1114_);
v_sz_1117_ = lean_array_size(v_args_1113_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1117_, v___x_1118_, v_args_1113_, v_snd_1116_);
v_fst_1120_ = lean_ctor_get(v___x_1119_, 0);
v_snd_1121_ = lean_ctor_get(v___x_1119_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v___x_1119_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
lean_dec(v___x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1125_, 0, v_info_1111_);
lean_ctor_set(v___x_1125_, 1, v_kind_1112_);
lean_ctor_set(v___x_1125_, 2, v_fst_1120_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_snd_1121_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_args_1113_);
lean_dec(v_kind_1112_);
lean_dec(v_info_1111_);
v_snd_1130_ = lean_ctor_get(v___x_1114_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1114_, 0);
lean_dec(v_unused_1139_);
v___x_1132_ = v___x_1114_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_dec(v___x_1114_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_val_1134_; lean_object* v___x_1136_; 
v_val_1134_ = lean_ctor_get(v_fst_1115_, 0);
lean_inc(v_val_1134_);
lean_dec_ref_known(v_fst_1115_, 1);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v_val_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_val_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_snd_1130_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v_fst_1141_; 
lean_inc(v_x_1109_);
v___x_1140_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1109_, v___y_1110_);
v_fst_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_fst_1141_);
if (lean_obj_tag(v_fst_1141_) == 0)
{
lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_snd_1142_ = lean_ctor_get(v___x_1140_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v___x_1140_, 0);
lean_dec(v_unused_1150_);
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_x_1109_);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_x_1109_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_snd_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_x_1109_);
v_snd_1151_ = lean_ctor_get(v___x_1140_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1140_, 0);
lean_dec(v_unused_1160_);
v___x_1153_ = v___x_1140_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_dec(v___x_1140_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_val_1155_; lean_object* v___x_1157_; 
v_val_1155_ = lean_ctor_get(v_fst_1141_, 0);
lean_inc(v_val_1155_);
lean_dec_ref_known(v_fst_1141_, 1);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_val_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_val_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_snd_1151_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1161_, size_t v_i_1162_, lean_object* v_bs_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_lt(v_i_1162_, v_sz_1161_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_bs_1163_);
lean_ctor_set(v___x_1166_, 1, v___y_1164_);
return v___x_1166_;
}
else
{
lean_object* v_v_1167_; lean_object* v___x_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v___x_1171_; lean_object* v_bs_x27_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_v_1167_ = lean_array_uget_borrowed(v_bs_1163_, v_i_1162_);
lean_inc(v_v_1167_);
v___x_1168_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1167_, v___y_1164_);
v_fst_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_fst_1169_);
v_snd_1170_ = lean_ctor_get(v___x_1168_, 1);
lean_inc(v_snd_1170_);
lean_dec_ref(v___x_1168_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v_bs_x27_1172_ = lean_array_uset(v_bs_1163_, v_i_1162_, v___x_1171_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1162_, v___x_1173_);
v___x_1175_ = lean_array_uset(v_bs_x27_1172_, v_i_1162_, v_fst_1169_);
v_i_1162_ = v___x_1174_;
v_bs_1163_ = v___x_1175_;
v___y_1164_ = v_snd_1170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1177_, lean_object* v_i_1178_, lean_object* v_bs_1179_, lean_object* v___y_1180_){
_start:
{
size_t v_sz_boxed_1181_; size_t v_i_boxed_1182_; lean_object* v_res_1183_; 
v_sz_boxed_1181_ = lean_unbox_usize(v_sz_1177_);
lean_dec(v_sz_1177_);
v_i_boxed_1182_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1181_, v_i_boxed_1182_, v_bs_1179_, v___y_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_fst_1187_; 
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1184_, v___x_1185_);
v_fst_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_fst_1187_);
lean_dec_ref(v___x_1186_);
return v_fst_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1188_, lean_object* v_x_1189_){
_start:
{
switch(lean_obj_tag(v_x_1189_))
{
case 2:
{
lean_object* v_info_1190_; lean_object* v_val_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_info_1190_ = lean_ctor_get(v_x_1189_, 0);
v_val_1191_ = lean_ctor_get(v_x_1189_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v_x_1189_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_val_1191_);
lean_inc(v_info_1190_);
lean_dec(v_x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1188_, v_info_1190_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_val_1191_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
case 3:
{
lean_object* v_info_1200_; lean_object* v_rawVal_1201_; lean_object* v_val_1202_; lean_object* v_preresolved_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
v_info_1200_ = lean_ctor_get(v_x_1189_, 0);
v_rawVal_1201_ = lean_ctor_get(v_x_1189_, 1);
v_val_1202_ = lean_ctor_get(v_x_1189_, 2);
v_preresolved_1203_ = lean_ctor_get(v_x_1189_, 3);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v_x_1189_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_preresolved_1203_);
lean_inc(v_val_1202_);
lean_inc(v_rawVal_1201_);
lean_inc(v_info_1200_);
lean_dec(v_x_1189_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1188_, v_info_1200_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_rawVal_1201_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_val_1202_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_preresolved_1203_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
case 1:
{
lean_object* v_info_1212_; lean_object* v_kind_1213_; lean_object* v_args_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_info_1212_ = lean_ctor_get(v_x_1189_, 0);
v_kind_1213_ = lean_ctor_get(v_x_1189_, 1);
v_args_1214_ = lean_ctor_get(v_x_1189_, 2);
v___x_1215_ = lean_array_get_size(v_args_1214_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_nat_dec_eq(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1229_; 
lean_inc_ref(v_args_1214_);
lean_inc(v_kind_1213_);
lean_inc(v_info_1212_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1230_ = lean_ctor_get(v_x_1189_, 2);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_x_1189_, 1);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_x_1189_, 0);
lean_dec(v_unused_1232_);
v___x_1219_ = v_x_1189_;
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_x_1189_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v_i_1222_; lean_object* v___x_1223_; lean_object* v_last_1224_; lean_object* v_args_1225_; lean_object* v___x_1227_; 
v___x_1221_ = lean_unsigned_to_nat(1u);
v_i_1222_ = lean_nat_sub(v___x_1215_, v___x_1221_);
v___x_1223_ = lean_array_fget_borrowed(v_args_1214_, v_i_1222_);
lean_inc(v___x_1223_);
v_last_1224_ = l_Lean_Syntax_updateTrailing(v_trailing_1188_, v___x_1223_);
v_args_1225_ = lean_array_fset(v_args_1214_, v_i_1222_, v_last_1224_);
lean_dec(v_i_1222_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 2, v_args_1225_);
v___x_1227_ = v___x_1219_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_info_1212_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_kind_1213_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_args_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_dec_ref(v_trailing_1188_);
return v_x_1189_;
}
}
default: 
{
lean_dec_ref(v_trailing_1188_);
return v_x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
return v_x_1233_;
}
else
{
lean_object* v_head_1235_; lean_object* v_tail_1236_; lean_object* v___x_1237_; 
v_head_1235_ = lean_ctor_get(v_x_1234_, 0);
lean_inc(v_head_1235_);
v_tail_1236_ = lean_ctor_get(v_x_1234_, 1);
lean_inc(v_tail_1236_);
lean_dec_ref_known(v_x_1234_, 2);
v___x_1237_ = l_Lean_Name_append(v_x_1233_, v_head_1235_);
v_x_1233_ = v___x_1237_;
v_x_1234_ = v_tail_1236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1241_, lean_object* v_nFields_x3f_1242_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v_nameComps_1244_; lean_object* v___x_1245_; lean_object* v_nPrefix_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_namePrefix_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_val_1243_ = lean_ctor_get(v_nFields_x3f_1242_, 0);
v_nameComps_1244_ = l_Lean_Name_components(v_n_1241_);
v___x_1245_ = l_List_lengthTR___redArg(v_nameComps_1244_);
v_nPrefix_1246_ = lean_nat_sub(v___x_1245_, v_val_1243_);
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(0);
v___x_1248_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1246_);
lean_inc(v_nameComps_1244_);
v___x_1249_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1244_, v_nameComps_1244_, v_nPrefix_1246_, v___x_1248_);
v_namePrefix_1250_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1247_, v___x_1249_);
v___x_1251_ = l_List_drop___redArg(v_nPrefix_1246_, v_nameComps_1244_);
lean_dec(v_nameComps_1244_);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_namePrefix_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Name_components(v_n_1241_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1254_, lean_object* v_nFields_x3f_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1254_, v_nFields_x3f_1255_);
lean_dec(v_nFields_x3f_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_panic_fn_borrowed(v___x_1258_, v_msg_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
return v_x_1260_;
}
else
{
lean_object* v_head_1262_; lean_object* v_tail_1263_; lean_object* v_startPos_1264_; lean_object* v_stopPos_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_head_1262_ = lean_ctor_get(v_x_1261_, 0);
v_tail_1263_ = lean_ctor_get(v_x_1261_, 1);
v_startPos_1264_ = lean_ctor_get(v_head_1262_, 1);
v_stopPos_1265_ = lean_ctor_get(v_head_1262_, 2);
v___x_1266_ = lean_nat_sub(v_stopPos_1265_, v_startPos_1264_);
v___x_1267_ = lean_nat_add(v_x_1260_, v___x_1266_);
lean_dec(v___x_1266_);
lean_dec(v_x_1260_);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_add(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
v_x_1260_ = v___x_1269_;
v_x_1261_ = v_tail_1263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1271_, v_x_1272_);
lean_dec(v_x_1272_);
return v_res_1273_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1275_ = lean_string_utf8_byte_size(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1277_);
lean_ctor_set(v___x_1279_, 2, v___x_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1281_, lean_object* v_pos_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
if (lean_obj_tag(v_a_1283_) == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = l_List_reverse___redArg(v_a_1284_);
return v___x_1285_;
}
else
{
lean_object* v_head_1286_; lean_object* v_tail_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1305_; 
v_head_1286_ = lean_ctor_get(v_a_1283_, 0);
v_tail_1287_ = lean_ctor_get(v_a_1283_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_a_1283_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1289_ = v_a_1283_;
v_isShared_1290_ = v_isSharedCheck_1305_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_tail_1287_);
lean_inc(v_head_1286_);
lean_dec(v_a_1283_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1305_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_stopPos_1291_; lean_object* v_startPos_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_info_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v_stopPos_1291_ = lean_ctor_get(v_head_1286_, 2);
lean_inc(v_stopPos_1291_);
lean_dec(v_head_1286_);
v_startPos_1292_ = lean_ctor_get(v_rawVal_1281_, 1);
v___x_1293_ = lean_nat_sub(v_stopPos_1291_, v_startPos_1292_);
lean_dec(v_stopPos_1291_);
v___x_1294_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___x_1295_ = lean_nat_add(v___x_1293_, v_pos_1282_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_add(v___x_1296_, v___x_1295_);
v_info_1298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1298_, 0, v___x_1294_);
lean_ctor_set(v_info_1298_, 1, v___x_1295_);
lean_ctor_set(v_info_1298_, 2, v___x_1294_);
lean_ctor_set(v_info_1298_, 3, v___x_1297_);
v___x_1299_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2));
v___x_1300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_info_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v_a_1284_);
lean_ctor_set(v___x_1289_, 0, v___x_1300_);
v___x_1302_ = v___x_1289_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1284_);
v___x_1302_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
v_a_1283_ = v_tail_1287_;
v_a_1284_ = v___x_1302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1306_, lean_object* v_pos_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1306_, v_pos_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_pos_1307_);
lean_dec_ref(v_rawVal_1306_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1311_, lean_object* v_pos_1312_, lean_object* v_trailing_1313_, lean_object* v_leading_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
if (lean_obj_tag(v_a_1315_) == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v_leading_1314_);
lean_dec_ref(v_trailing_1313_);
v___x_1317_ = l_List_reverse___redArg(v_a_1316_);
return v___x_1317_;
}
else
{
lean_object* v_head_1318_; lean_object* v_snd_1319_; lean_object* v_tail_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1350_; 
v_head_1318_ = lean_ctor_get(v_a_1315_, 0);
lean_inc(v_head_1318_);
v_snd_1319_ = lean_ctor_get(v_head_1318_, 1);
lean_inc(v_snd_1319_);
v_tail_1320_ = lean_ctor_get(v_a_1315_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_a_1315_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v_a_1315_, 0);
lean_dec(v_unused_1351_);
v___x_1322_ = v_a_1315_;
v_isShared_1323_ = v_isSharedCheck_1350_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_tail_1320_);
lean_dec(v_a_1315_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1350_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_fst_1324_; lean_object* v_startPos_1325_; lean_object* v_stopPos_1326_; lean_object* v_startPos_1327_; lean_object* v_stopPos_1328_; lean_object* v_off_1329_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1344_; lean_object* v___x_1347_; uint8_t v_decide_1348_; 
v_fst_1324_ = lean_ctor_get(v_head_1318_, 0);
lean_inc(v_fst_1324_);
lean_dec(v_head_1318_);
v_startPos_1325_ = lean_ctor_get(v_snd_1319_, 1);
v_stopPos_1326_ = lean_ctor_get(v_snd_1319_, 2);
v_startPos_1327_ = lean_ctor_get(v_rawVal_1311_, 1);
v_stopPos_1328_ = lean_ctor_get(v_rawVal_1311_, 2);
v_off_1329_ = lean_nat_sub(v_startPos_1325_, v_startPos_1327_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v_decide_1348_ = lean_nat_dec_eq(v_off_1329_, v___x_1347_);
if (v_decide_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___y_1344_ = v___x_1349_;
goto v___jp_1343_;
}
else
{
lean_inc_ref(v_leading_1314_);
v___y_1344_ = v_leading_1314_;
goto v___jp_1343_;
}
v___jp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_info_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1333_ = lean_nat_add(v_off_1329_, v_pos_1312_);
lean_dec(v_off_1329_);
v___x_1334_ = lean_nat_sub(v_stopPos_1326_, v_startPos_1325_);
v___x_1335_ = lean_nat_add(v___x_1334_, v___x_1333_);
lean_dec(v___x_1334_);
v_info_1336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1336_, 0, v___y_1331_);
lean_ctor_set(v_info_1336_, 1, v___x_1333_);
lean_ctor_set(v_info_1336_, 2, v___y_1332_);
lean_ctor_set(v_info_1336_, 3, v___x_1335_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1338_, 0, v_info_1336_);
lean_ctor_set(v___x_1338_, 1, v_snd_1319_);
lean_ctor_set(v___x_1338_, 2, v_fst_1324_);
lean_ctor_set(v___x_1338_, 3, v___x_1337_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v_a_1316_);
lean_ctor_set(v___x_1322_, 0, v___x_1338_);
v___x_1340_ = v___x_1322_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1316_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v_a_1315_ = v_tail_1320_;
v_a_1316_ = v___x_1340_;
goto _start;
}
}
v___jp_1343_:
{
uint8_t v_decide_1345_; 
v_decide_1345_ = lean_nat_dec_eq(v_stopPos_1326_, v_stopPos_1328_);
if (v_decide_1345_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___y_1331_ = v___y_1344_;
v___y_1332_ = v___x_1346_;
goto v___jp_1330_;
}
else
{
lean_inc_ref(v_trailing_1313_);
v___y_1331_ = v___y_1344_;
v___y_1332_ = v_trailing_1313_;
goto v___jp_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1352_, lean_object* v_pos_1353_, lean_object* v_trailing_1354_, lean_object* v_leading_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1352_, v_pos_1353_, v_trailing_1354_, v_leading_1355_, v_a_1356_, v_a_1357_);
lean_dec(v_pos_1353_);
lean_dec_ref(v_rawVal_1352_);
return v_res_1358_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__5(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1367_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1368_ = lean_unsigned_to_nat(9u);
v___x_1369_ = lean_unsigned_to_nat(342u);
v___x_1370_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1371_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1372_ = l_mkPanicMessageWithDecl(v___x_1371_, v___x_1370_, v___x_1369_, v___x_1368_, v___x_1367_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1373_, lean_object* v_nFields_x3f_1374_){
_start:
{
if (lean_obj_tag(v_stx_1373_) == 3)
{
lean_object* v_info_1375_; 
v_info_1375_ = lean_ctor_get(v_stx_1373_, 0);
lean_inc(v_info_1375_);
if (lean_obj_tag(v_info_1375_) == 0)
{
lean_object* v_rawVal_1376_; lean_object* v_val_1377_; lean_object* v_leading_1378_; lean_object* v_pos_1379_; lean_object* v_trailing_1380_; lean_object* v_rawComps_1381_; uint8_t v___x_1382_; 
v_rawVal_1376_ = lean_ctor_get(v_stx_1373_, 1);
lean_inc_ref_n(v_rawVal_1376_, 2);
v_val_1377_ = lean_ctor_get(v_stx_1373_, 2);
lean_inc(v_val_1377_);
lean_dec_ref_known(v_stx_1373_, 4);
v_leading_1378_ = lean_ctor_get(v_info_1375_, 0);
lean_inc_ref(v_leading_1378_);
v_pos_1379_ = lean_ctor_get(v_info_1375_, 1);
lean_inc(v_pos_1379_);
v_trailing_1380_ = lean_ctor_get(v_info_1375_, 2);
lean_inc_ref(v_trailing_1380_);
lean_dec_ref_known(v_info_1375_, 4);
v_rawComps_1381_ = l_Lean_Syntax_splitNameLit(v_rawVal_1376_);
v___x_1382_ = l_List_isEmpty___redArg(v_rawComps_1381_);
if (v___x_1382_ == 0)
{
lean_object* v_val_1383_; lean_object* v_nameComps_1384_; lean_object* v___y_1386_; 
v_val_1383_ = l_Lean_Name_eraseMacroScopes(v_val_1377_);
lean_dec(v_val_1377_);
v_nameComps_1384_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1383_, v_nFields_x3f_1374_);
if (lean_obj_tag(v_nFields_x3f_1374_) == 1)
{
lean_object* v_val_1400_; lean_object* v_str_1401_; lean_object* v_startPos_1402_; lean_object* v_stopPos_1403_; lean_object* v___x_1404_; lean_object* v_nPrefix_1405_; lean_object* v___y_1407_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_prefixSz_1413_; lean_object* v___x_1414_; lean_object* v_prefixSz_1415_; lean_object* v___y_1417_; uint8_t v___x_1422_; 
v_val_1400_ = lean_ctor_get(v_nFields_x3f_1374_, 0);
v_str_1401_ = lean_ctor_get(v_rawVal_1376_, 0);
v_startPos_1402_ = lean_ctor_get(v_rawVal_1376_, 1);
v_stopPos_1403_ = lean_ctor_get(v_rawVal_1376_, 2);
v___x_1404_ = l_List_lengthTR___redArg(v_rawComps_1381_);
v_nPrefix_1405_ = lean_nat_sub(v___x_1404_, v_val_1400_);
lean_dec(v___x_1404_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1405_);
lean_inc(v_rawComps_1381_);
v___x_1412_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1381_, v_rawComps_1381_, v_nPrefix_1405_, v___x_1411_);
v_prefixSz_1413_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1410_, v___x_1412_);
lean_dec(v___x_1412_);
v___x_1414_ = lean_unsigned_to_nat(1u);
v_prefixSz_1415_ = lean_nat_sub(v_prefixSz_1413_, v___x_1414_);
lean_dec(v_prefixSz_1413_);
v___x_1422_ = lean_nat_dec_le(v_prefixSz_1415_, v___x_1410_);
if (v___x_1422_ == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_nat_dec_le(v_stopPos_1403_, v_startPos_1402_);
if (v___x_1423_ == 0)
{
lean_inc(v_startPos_1402_);
v___y_1417_ = v_startPos_1402_;
goto v___jp_1416_;
}
else
{
lean_inc(v_stopPos_1403_);
v___y_1417_ = v_stopPos_1403_;
goto v___jp_1416_;
}
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_prefixSz_1415_);
v___x_1424_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___y_1407_ = v___x_1424_;
goto v___jp_1406_;
}
v___jp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = l_List_drop___redArg(v_nPrefix_1405_, v_rawComps_1381_);
lean_dec(v_rawComps_1381_);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___y_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___y_1386_ = v___x_1409_;
goto v___jp_1385_;
}
v___jp_1416_:
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_nat_add(v_startPos_1402_, v_prefixSz_1415_);
lean_dec(v_prefixSz_1415_);
v___x_1419_ = lean_nat_dec_le(v_stopPos_1403_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_inc_ref(v_str_1401_);
v___x_1420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1420_, 0, v_str_1401_);
lean_ctor_set(v___x_1420_, 1, v___y_1417_);
lean_ctor_set(v___x_1420_, 2, v___x_1418_);
v___y_1407_ = v___x_1420_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1421_; 
lean_dec(v___x_1418_);
lean_inc(v_stopPos_1403_);
lean_inc_ref(v_str_1401_);
v___x_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_str_1401_);
lean_ctor_set(v___x_1421_, 1, v___y_1417_);
lean_ctor_set(v___x_1421_, 2, v_stopPos_1403_);
v___y_1407_ = v___x_1421_;
goto v___jp_1406_;
}
}
}
else
{
v___y_1386_ = v_rawComps_1381_;
goto v___jp_1385_;
}
v___jp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = l_List_lengthTR___redArg(v_nameComps_1384_);
v___x_1388_ = l_List_lengthTR___redArg(v___y_1386_);
v___x_1389_ = lean_nat_dec_eq(v___x_1387_, v___x_1388_);
lean_dec(v___x_1388_);
lean_dec(v___x_1387_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v___y_1386_);
lean_dec(v_nameComps_1384_);
lean_dec_ref(v_trailing_1380_);
lean_dec(v_pos_1379_);
lean_dec_ref(v_leading_1378_);
lean_dec_ref(v_rawVal_1376_);
v___x_1390_ = lean_box(0);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_comps_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_seps_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc(v___y_1386_);
v___x_1391_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1384_, v___y_1386_);
v___x_1392_ = lean_box(0);
v_comps_1393_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1376_, v_pos_1379_, v_trailing_1380_, v_leading_1378_, v___x_1391_, v___x_1392_);
v___x_1394_ = lean_array_mk(v___y_1386_);
v___x_1395_ = lean_array_pop(v___x_1394_);
v___x_1396_ = lean_array_to_list(v___x_1395_);
v_seps_1397_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1376_, v_pos_1379_, v___x_1396_, v___x_1392_);
lean_dec(v_pos_1379_);
lean_dec_ref(v_rawVal_1376_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_comps_1393_);
lean_ctor_set(v___x_1398_, 1, v_seps_1397_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_rawComps_1381_);
lean_dec_ref(v_trailing_1380_);
lean_dec(v_pos_1379_);
lean_dec_ref(v_leading_1378_);
lean_dec(v_val_1377_);
lean_dec_ref(v_rawVal_1376_);
v___x_1425_ = lean_box(0);
return v___x_1425_;
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_info_1375_);
lean_dec_ref_known(v_stx_1373_, 4);
v___x_1426_ = lean_box(0);
return v___x_1426_;
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v_stx_1373_);
v___x_1427_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__5, &l_Lean_Syntax_identComponents_x3f___closed__5_once, _init_l_Lean_Syntax_identComponents_x3f___closed__5);
v___x_1428_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1427_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1429_, lean_object* v_nFields_x3f_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Syntax_identComponents_x3f(v_stx_1429_, v_nFields_x3f_1430_);
lean_dec(v_nFields_x3f_1430_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1432_, lean_object* v_nFields_x3f_1433_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1433_) == 1)
{
lean_object* v_val_1434_; lean_object* v_nameComps_1435_; lean_object* v___x_1436_; lean_object* v_nPrefix_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_namePrefix_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_val_1434_ = lean_ctor_get(v_nFields_x3f_1433_, 0);
v_nameComps_1435_ = l_Lean_Name_components(v_n_1432_);
v___x_1436_ = l_List_lengthTR___redArg(v_nameComps_1435_);
v_nPrefix_1437_ = lean_nat_sub(v___x_1436_, v_val_1434_);
lean_dec(v___x_1436_);
v___x_1438_ = lean_box(0);
v___x_1439_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1437_);
lean_inc(v_nameComps_1435_);
v___x_1440_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1435_, v_nameComps_1435_, v_nPrefix_1437_, v___x_1439_);
v_namePrefix_1441_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1438_, v___x_1440_);
v___x_1442_ = l_List_drop___redArg(v_nPrefix_1437_, v_nameComps_1435_);
lean_dec(v_nameComps_1435_);
v___x_1443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_namePrefix_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Name_components(v_n_1432_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1445_, lean_object* v_nFields_x3f_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1445_, v_nFields_x3f_1446_);
lean_dec(v_nFields_x3f_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_panic_fn_borrowed(v___x_1449_, v_msg_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
if (lean_obj_tag(v_a_1452_) == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_info_1451_);
v___x_1454_ = l_List_reverse___redArg(v_a_1453_);
return v___x_1454_;
}
else
{
lean_object* v_head_1455_; lean_object* v_tail_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1471_; 
v_head_1455_ = lean_ctor_get(v_a_1452_, 0);
v_tail_1456_ = lean_ctor_get(v_a_1452_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_a_1452_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1458_ = v_a_1452_;
v_isShared_1459_ = v_isSharedCheck_1471_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_tail_1456_);
lean_inc(v_head_1455_);
lean_dec(v_a_1452_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1471_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1460_ = 1;
lean_inc(v_head_1455_);
v___x_1461_ = l_Lean_Name_toString(v_head_1455_, v___x_1460_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_string_utf8_byte_size(v___x_1461_);
v___x_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1461_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = lean_box(0);
lean_inc(v_info_1451_);
v___x_1466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1466_, 0, v_info_1451_);
lean_ctor_set(v___x_1466_, 1, v___x_1464_);
lean_ctor_set(v___x_1466_, 2, v_head_1455_);
lean_ctor_set(v___x_1466_, 3, v___x_1465_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v_a_1453_);
lean_ctor_set(v___x_1458_, 0, v___x_1466_);
v___x_1468_ = v___x_1458_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_a_1453_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
v_a_1452_ = v_tail_1456_;
v_a_1453_ = v___x_1468_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1474_ = lean_unsigned_to_nat(9u);
v___x_1475_ = lean_unsigned_to_nat(377u);
v___x_1476_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1477_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1478_ = l_mkPanicMessageWithDecl(v___x_1477_, v___x_1476_, v___x_1475_, v___x_1474_, v___x_1473_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1479_, lean_object* v_nFields_x3f_1480_){
_start:
{
if (lean_obj_tag(v_stx_1479_) == 3)
{
lean_object* v_info_1481_; lean_object* v_rawVal_1482_; lean_object* v_val_1483_; lean_object* v_val_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_info_1481_ = lean_ctor_get(v_stx_1479_, 0);
lean_inc(v_info_1481_);
v_rawVal_1482_ = lean_ctor_get(v_stx_1479_, 1);
v_val_1483_ = lean_ctor_get(v_stx_1479_, 2);
v_val_1484_ = l_Lean_Name_eraseMacroScopes(v_val_1483_);
v___x_1485_ = l_Lean_Name_getNumParts(v_val_1484_);
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_dec_le(v___x_1485_, v___x_1486_);
lean_dec(v___x_1485_);
if (v___x_1487_ == 0)
{
if (lean_obj_tag(v_info_1481_) == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Syntax_identComponents_x3f(v_stx_1479_, v_nFields_x3f_1480_);
if (lean_obj_tag(v___x_1488_) == 1)
{
lean_object* v_val_1489_; lean_object* v_fst_1490_; 
lean_dec_ref_known(v_info_1481_, 4);
lean_dec(v_val_1484_);
v_val_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v_fst_1490_ = lean_ctor_get(v_val_1489_, 0);
lean_inc(v_fst_1490_);
lean_dec(v_val_1489_);
return v_fst_1490_;
}
else
{
lean_object* v_nameComps_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v___x_1488_);
v_nameComps_1491_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1484_, v_nFields_x3f_1480_);
v___x_1492_ = lean_box(0);
v___x_1493_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1481_, v_nameComps_1491_, v___x_1492_);
return v___x_1493_;
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref_known(v_stx_1479_, 4);
v___x_1494_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1484_, v_nFields_x3f_1480_);
v___x_1495_ = lean_box(0);
v___x_1496_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1481_, v___x_1494_, v___x_1495_);
return v___x_1496_;
}
}
else
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
lean_inc_ref(v_rawVal_1482_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_stx_1479_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; 
v_unused_1506_ = lean_ctor_get(v_stx_1479_, 3);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_stx_1479_, 2);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_stx_1479_, 1);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_stx_1479_, 0);
lean_dec(v_unused_1509_);
v___x_1498_ = v_stx_1479_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_stx_1479_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_box(0);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 3, v___x_1500_);
lean_ctor_set(v___x_1498_, 2, v_val_1484_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_info_1481_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_rawVal_1482_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_val_1484_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v___x_1500_);
return v___x_1503_;
}
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v_stx_1479_);
v___x_1510_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1511_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1512_, lean_object* v_nFields_x3f_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Syntax_identComponents(v_stx_1512_, v_nFields_x3f_1513_);
lean_dec(v_nFields_x3f_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1515_, uint8_t v_firstChoiceOnly_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1517_, 0, v_stx_1515_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*1, v_firstChoiceOnly_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1518_, lean_object* v_firstChoiceOnly_1519_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1520_; lean_object* v_res_1521_; 
v_firstChoiceOnly_boxed_1520_ = lean_unbox(v_firstChoiceOnly_1519_);
v_res_1521_ = l_Lean_Syntax_topDown(v_stx_1518_, v_firstChoiceOnly_boxed_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1522_, lean_object* v_____r_1523_, lean_object* v_b_1524_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1524_);
v___x_1526_ = lean_apply_2(v_toPure_1522_, lean_box(0), v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1527_, lean_object* v_toPure_1528_, lean_object* v_____s_1529_){
_start:
{
lean_object* v_fst_1530_; 
v_fst_1530_ = lean_ctor_get(v_____s_1529_, 0);
if (lean_obj_tag(v_fst_1530_) == 0)
{
lean_object* v_snd_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_toPure_1528_);
v_snd_1531_ = lean_ctor_get(v_____s_1529_, 1);
lean_inc(v_snd_1531_);
lean_dec_ref(v_____s_1529_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_apply_2(v___f_1527_, v___x_1532_, v_snd_1531_);
return v___x_1533_;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1535_; 
lean_inc_ref(v_fst_1530_);
lean_dec_ref(v_____s_1529_);
lean_dec(v___f_1527_);
v_val_1534_ = lean_ctor_get(v_fst_1530_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v_fst_1530_, 1);
v___x_1535_ = lean_apply_2(v_toPure_1528_, lean_box(0), v_val_1534_);
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1536_, lean_object* v_toPure_1537_, lean_object* v___x_1538_, lean_object* v_____do__lift_1539_){
_start:
{
if (lean_obj_tag(v_____do__lift_1539_) == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v___x_1538_);
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_____do__lift_1539_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_snd_1536_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
v___x_1543_ = lean_apply_2(v_toPure_1537_, lean_box(0), v___x_1542_);
return v___x_1543_;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_snd_1536_);
v_a_1544_ = lean_ctor_get(v_____do__lift_1539_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_____do__lift_1539_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1546_ = v_____do__lift_1539_;
v_isShared_1547_ = v_isSharedCheck_1553_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v_____do__lift_1539_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1553_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1538_);
lean_ctor_set(v___x_1548_, 1, v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_apply_2(v_toPure_1537_, lean_box(0), v___x_1550_);
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1554_, lean_object* v___x_1555_, lean_object* v_inst_1556_, lean_object* v_f_1557_, lean_object* v_firstChoiceOnly_1558_, lean_object* v_toBind_1559_, lean_object* v_a_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1563_; lean_object* v_res_1564_; 
v_firstChoiceOnly_boxed_1563_ = lean_unbox(v_firstChoiceOnly_1558_);
v_res_1564_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1554_, v___x_1555_, v_inst_1556_, v_f_1557_, v_firstChoiceOnly_boxed_1563_, v_toBind_1559_, v_a_1560_, v_x_1561_, v___y_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1568_, lean_object* v_stx_1569_, lean_object* v_inst_1570_, lean_object* v_f_1571_, uint8_t v_firstChoiceOnly_1572_, lean_object* v_toBind_1573_, lean_object* v___f_1574_, lean_object* v___x_1575_, lean_object* v___f_1576_, lean_object* v_____do__lift_1577_){
_start:
{
if (lean_obj_tag(v_____do__lift_1577_) == 0)
{
lean_object* v___x_1578_; 
lean_dec(v___f_1576_);
lean_dec(v___f_1574_);
lean_dec(v_toBind_1573_);
lean_dec(v_f_1571_);
lean_dec_ref(v_inst_1570_);
lean_dec(v_stx_1569_);
v___x_1578_ = lean_apply_2(v_toPure_1568_, lean_box(0), v_____do__lift_1577_);
return v___x_1578_;
}
else
{
if (lean_obj_tag(v_stx_1569_) == 1)
{
lean_object* v_a_1579_; lean_object* v_kind_1580_; lean_object* v_args_1581_; 
lean_dec(v___f_1576_);
v_a_1579_ = lean_ctor_get(v_____do__lift_1577_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v_____do__lift_1577_, 1);
v_kind_1580_ = lean_ctor_get(v_stx_1569_, 1);
lean_inc(v_kind_1580_);
v_args_1581_ = lean_ctor_get(v_stx_1569_, 2);
lean_inc_ref(v_args_1581_);
lean_dec_ref_known(v_stx_1569_, 3);
if (v_firstChoiceOnly_1572_ == 0)
{
lean_dec(v_kind_1580_);
goto v___jp_1582_;
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1592_ = lean_name_eq(v_kind_1580_, v___x_1591_);
lean_dec(v_kind_1580_);
if (v___x_1592_ == 0)
{
goto v___jp_1582_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v___f_1574_);
lean_dec(v_toBind_1573_);
lean_dec(v_toPure_1568_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_array_get(v___x_1575_, v_args_1581_, v___x_1593_);
lean_dec_ref(v_args_1581_);
v___x_1595_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1570_, v_f_1571_, v_firstChoiceOnly_1572_, v___x_1594_, v_a_1579_);
return v___x_1595_;
}
}
v___jp_1582_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_box(v_firstChoiceOnly_1572_);
lean_inc(v_toBind_1573_);
lean_inc_ref(v_inst_1570_);
v___f_1585_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1585_, 0, v_toPure_1568_);
lean_closure_set(v___f_1585_, 1, v___x_1583_);
lean_closure_set(v___f_1585_, 2, v_inst_1570_);
lean_closure_set(v___f_1585_, 3, v_f_1571_);
lean_closure_set(v___f_1585_, 4, v___x_1584_);
lean_closure_set(v___f_1585_, 5, v_toBind_1573_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1583_);
lean_ctor_set(v___x_1586_, 1, v_a_1579_);
v_sz_1587_ = lean_array_size(v_args_1581_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1570_, v_args_1581_, v___f_1585_, v_sz_1587_, v___x_1588_, v___x_1586_);
v___x_1590_ = lean_apply_4(v_toBind_1573_, lean_box(0), lean_box(0), v___x_1589_, v___f_1574_);
return v___x_1590_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v___f_1574_);
lean_dec(v_toBind_1573_);
lean_dec(v_f_1571_);
lean_dec_ref(v_inst_1570_);
lean_dec(v_stx_1569_);
lean_dec(v_toPure_1568_);
v_a_1596_ = lean_ctor_get(v_____do__lift_1577_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v_____do__lift_1577_, 1);
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_apply_2(v___f_1576_, v___x_1597_, v_a_1596_);
return v___x_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1599_, lean_object* v_stx_1600_, lean_object* v_inst_1601_, lean_object* v_f_1602_, lean_object* v_firstChoiceOnly_1603_, lean_object* v_toBind_1604_, lean_object* v___f_1605_, lean_object* v___x_1606_, lean_object* v___f_1607_, lean_object* v_____do__lift_1608_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1609_; lean_object* v_res_1610_; 
v_firstChoiceOnly_boxed_1609_ = lean_unbox(v_firstChoiceOnly_1603_);
v_res_1610_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1599_, v_stx_1600_, v_inst_1601_, v_f_1602_, v_firstChoiceOnly_boxed_1609_, v_toBind_1604_, v___f_1605_, v___x_1606_, v___f_1607_, v_____do__lift_1608_);
lean_dec(v___x_1606_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1611_, lean_object* v_f_1612_, uint8_t v_firstChoiceOnly_1613_, lean_object* v_stx_1614_, lean_object* v_b_1615_){
_start:
{
lean_object* v_toApplicative_1616_; lean_object* v_toBind_1617_; lean_object* v_toPure_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; 
v_toApplicative_1616_ = lean_ctor_get(v_inst_1611_, 0);
v_toBind_1617_ = lean_ctor_get(v_inst_1611_, 1);
lean_inc_n(v_toBind_1617_, 2);
v_toPure_1618_ = lean_ctor_get(v_toApplicative_1616_, 1);
lean_inc_n(v_toPure_1618_, 3);
v___x_1619_ = lean_box(0);
lean_inc(v_f_1612_);
lean_inc(v_stx_1614_);
v___x_1620_ = lean_apply_2(v_f_1612_, v_stx_1614_, v_b_1615_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1621_, 0, v_toPure_1618_);
lean_inc_ref(v___f_1621_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1622_, 0, v___f_1621_);
lean_closure_set(v___f_1622_, 1, v_toPure_1618_);
v___x_1623_ = lean_box(v_firstChoiceOnly_1613_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1624_, 0, v_toPure_1618_);
lean_closure_set(v___f_1624_, 1, v_stx_1614_);
lean_closure_set(v___f_1624_, 2, v_inst_1611_);
lean_closure_set(v___f_1624_, 3, v_f_1612_);
lean_closure_set(v___f_1624_, 4, v___x_1623_);
lean_closure_set(v___f_1624_, 5, v_toBind_1617_);
lean_closure_set(v___f_1624_, 6, v___f_1622_);
lean_closure_set(v___f_1624_, 7, v___x_1619_);
lean_closure_set(v___f_1624_, 8, v___f_1621_);
v___x_1625_ = lean_apply_4(v_toBind_1617_, lean_box(0), lean_box(0), v___x_1620_, v___f_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1626_, lean_object* v___x_1627_, lean_object* v_inst_1628_, lean_object* v_f_1629_, uint8_t v_firstChoiceOnly_1630_, lean_object* v_toBind_1631_, lean_object* v_a_1632_, lean_object* v_x_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_snd_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_snd_1635_ = lean_ctor_get(v___y_1634_, 1);
lean_inc_n(v_snd_1635_, 2);
lean_dec_ref(v___y_1634_);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1636_, 0, v_snd_1635_);
lean_closure_set(v___f_1636_, 1, v_toPure_1626_);
lean_closure_set(v___f_1636_, 2, v___x_1627_);
v___x_1637_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1628_, v_f_1629_, v_firstChoiceOnly_1630_, v_a_1632_, v_snd_1635_);
v___x_1638_ = lean_apply_4(v_toBind_1631_, lean_box(0), lean_box(0), v___x_1637_, v___f_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1639_, lean_object* v_f_1640_, lean_object* v_firstChoiceOnly_1641_, lean_object* v_stx_1642_, lean_object* v_b_1643_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1644_; lean_object* v_res_1645_; 
v_firstChoiceOnly_boxed_1644_ = lean_unbox(v_firstChoiceOnly_1641_);
v_res_1645_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1639_, v_f_1640_, v_firstChoiceOnly_boxed_1644_, v_stx_1642_, v_b_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1646_, lean_object* v_inst_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_f_1649_, uint8_t v_firstChoiceOnly_1650_, lean_object* v_stx_1651_, lean_object* v_b_1652_, lean_object* v_inst_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1647_, v_f_1649_, v_firstChoiceOnly_1650_, v_stx_1651_, v_b_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1655_, lean_object* v_inst_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_f_1658_, lean_object* v_firstChoiceOnly_1659_, lean_object* v_stx_1660_, lean_object* v_b_1661_, lean_object* v_inst_1662_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1663_; lean_object* v_res_1664_; 
v_firstChoiceOnly_boxed_1663_ = lean_unbox(v_firstChoiceOnly_1659_);
v_res_1664_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1655_, v_inst_1656_, v_00_u03b2_1657_, v_f_1658_, v_firstChoiceOnly_boxed_1663_, v_stx_1660_, v_b_1661_, v_inst_1662_);
lean_dec(v_inst_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1665_, lean_object* v_____do__lift_1666_){
_start:
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v_____do__lift_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v_____do__lift_1666_);
v___x_1668_ = lean_apply_2(v_toPure_1665_, lean_box(0), v_a_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1669_, lean_object* v_toBind_1670_, lean_object* v___f_1671_, lean_object* v_00_u03b2_1672_, lean_object* v_x_1673_, lean_object* v_init_1674_, lean_object* v_f_1675_){
_start:
{
uint8_t v_firstChoiceOnly_1676_; lean_object* v_stx_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_firstChoiceOnly_1676_ = lean_ctor_get_uint8(v_x_1673_, sizeof(void*)*1);
v_stx_1677_ = lean_ctor_get(v_x_1673_, 0);
lean_inc(v_stx_1677_);
lean_dec_ref(v_x_1673_);
v___x_1678_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1669_, v_f_1675_, v_firstChoiceOnly_1676_, v_stx_1677_, v_init_1674_);
v___x_1679_ = lean_apply_4(v_toBind_1670_, lean_box(0), lean_box(0), v___x_1678_, v___f_1671_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1680_){
_start:
{
lean_object* v_toApplicative_1681_; lean_object* v_toBind_1682_; lean_object* v_toPure_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; 
v_toApplicative_1681_ = lean_ctor_get(v_inst_1680_, 0);
v_toBind_1682_ = lean_ctor_get(v_inst_1680_, 1);
lean_inc(v_toBind_1682_);
v_toPure_1683_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_inc(v_toPure_1683_);
v___f_1684_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1684_, 0, v_toPure_1683_);
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1685_, 0, v_inst_1680_);
lean_closure_set(v___f_1685_, 1, v_toBind_1682_);
lean_closure_set(v___f_1685_, 2, v___f_1684_);
return v___f_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1686_, lean_object* v_inst_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1690_, lean_object* v_val_1691_){
_start:
{
if (lean_obj_tag(v_info_1690_) == 0)
{
lean_object* v_leading_1692_; lean_object* v_trailing_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_leading_1692_ = lean_ctor_get(v_info_1690_, 0);
lean_inc_ref(v_leading_1692_);
v_trailing_1693_ = lean_ctor_get(v_info_1690_, 2);
lean_inc_ref(v_trailing_1693_);
lean_dec_ref_known(v_info_1690_, 4);
v___x_1694_ = lean_substring_tostring(v_leading_1692_);
v___x_1695_ = lean_string_append(v___x_1694_, v_val_1691_);
v___x_1696_ = lean_substring_tostring(v_trailing_1693_);
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
lean_dec_ref(v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v_info_1690_);
v___x_1698_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1699_ = lean_string_append(v___x_1698_, v_val_1691_);
v___x_1700_ = lean_string_append(v___x_1699_, v___x_1698_);
return v___x_1700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1701_, lean_object* v_val_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1701_, v_val_1702_);
lean_dec_ref(v_val_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1704_, lean_object* v_as_1705_, size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_b_1708_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_b_1708_);
return v___x_1710_;
}
else
{
lean_object* v_snd_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1738_; 
v_snd_1711_ = lean_ctor_get(v_b_1708_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_b_1708_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v_b_1708_, 0);
lean_dec(v_unused_1739_);
v___x_1713_ = v_b_1708_;
v_isShared_1714_ = v_isSharedCheck_1738_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_snd_1711_);
lean_dec(v_b_1708_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1738_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_a_1715_; lean_object* v___x_1716_; 
v_a_1715_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
lean_inc(v_snd_1711_);
lean_inc(v_a_1715_);
v___x_1716_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1704_, v_a_1715_, v_snd_1711_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
lean_del_object(v___x_1713_);
lean_dec(v_snd_1711_);
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
else
{
lean_object* v_val_1718_; 
v_val_1718_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_val_1718_);
if (lean_obj_tag(v_val_1718_) == 0)
{
lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1728_; 
v_isSharedCheck_1728_ = !lean_is_exclusive(v_val_1718_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_val_1718_, 0);
lean_dec(v_unused_1729_);
v___x_1720_ = v_val_1718_;
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
else
{
lean_dec(v_val_1718_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1716_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_snd_1711_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 1);
lean_ctor_set(v___x_1720_, 0, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec_ref_known(v___x_1716_, 1);
lean_dec(v_snd_1711_);
v_a_1730_ = lean_ctor_get(v_val_1718_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v_val_1718_, 1);
v___x_1731_ = lean_box(0);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_a_1730_);
lean_ctor_set(v___x_1713_, 0, v___x_1731_);
v___x_1733_ = v___x_1713_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_a_1730_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
size_t v___x_1734_; size_t v___x_1735_; 
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1707_, v___x_1734_);
v_i_1707_ = v___x_1735_;
v_b_1708_ = v___x_1733_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1740_, lean_object* v_a_1741_, lean_object* v_b_1742_){
_start:
{
lean_object* v_array_1743_; lean_object* v_start_1744_; lean_object* v_stop_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1764_; 
v_array_1743_ = lean_ctor_get(v_a_1741_, 0);
v_start_1744_ = lean_ctor_get(v_a_1741_, 1);
v_stop_1745_ = lean_ctor_get(v_a_1741_, 2);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_a_1741_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1747_ = v_a_1741_;
v_isShared_1748_ = v_isSharedCheck_1764_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_stop_1745_);
lean_inc(v_start_1744_);
lean_inc(v_array_1743_);
lean_dec(v_a_1741_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1764_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_nat_dec_lt(v_start_1744_, v_stop_1745_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_del_object(v___x_1747_);
lean_dec(v_stop_1745_);
lean_dec(v_start_1744_);
lean_dec_ref(v_array_1743_);
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_b_1742_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_array_fget_borrowed(v_array_1743_, v_start_1744_);
lean_inc(v___x_1751_);
v___x_1752_ = l_Lean_Syntax_reprint(v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; 
lean_del_object(v___x_1747_);
lean_dec(v_stop_1745_);
lean_dec(v_start_1744_);
lean_dec_ref(v_array_1743_);
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
else
{
lean_object* v_val_1754_; uint8_t v___x_1755_; 
v_val_1754_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_val_1754_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1755_ = lean_string_dec_eq(v_val_1740_, v_val_1754_);
lean_dec(v_val_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_del_object(v___x_1747_);
lean_dec(v_stop_1745_);
lean_dec(v_start_1744_);
lean_dec_ref(v_array_1743_);
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_start_1744_, v___x_1758_);
lean_dec(v_start_1744_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1759_);
v___x_1761_ = v___x_1747_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_array_1743_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_stop_1745_);
v___x_1761_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
v_a_1741_ = v___x_1761_;
v_b_1742_ = v___x_1757_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1765_, lean_object* v_stx_1766_, lean_object* v_b_1767_){
_start:
{
lean_object* v_b_1769_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___x_1783_; lean_object* v_a_1785_; 
v___x_1783_ = lean_box(0);
switch(lean_obj_tag(v_stx_1766_))
{
case 2:
{
lean_object* v_info_1794_; lean_object* v_val_1795_; lean_object* v___x_1796_; lean_object* v_s_1797_; 
v_info_1794_ = lean_ctor_get(v_stx_1766_, 0);
v_val_1795_ = lean_ctor_get(v_stx_1766_, 1);
lean_inc(v_info_1794_);
v___x_1796_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1794_, v_val_1795_);
v_s_1797_ = lean_string_append(v_b_1767_, v___x_1796_);
lean_dec_ref(v___x_1796_);
v_a_1785_ = v_s_1797_;
goto v___jp_1784_;
}
case 3:
{
lean_object* v_rawVal_1798_; lean_object* v_info_1799_; lean_object* v_str_1800_; lean_object* v_startPos_1801_; lean_object* v_stopPos_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_s_1805_; 
v_rawVal_1798_ = lean_ctor_get(v_stx_1766_, 1);
v_info_1799_ = lean_ctor_get(v_stx_1766_, 0);
v_str_1800_ = lean_ctor_get(v_rawVal_1798_, 0);
v_startPos_1801_ = lean_ctor_get(v_rawVal_1798_, 1);
v_stopPos_1802_ = lean_ctor_get(v_rawVal_1798_, 2);
v___x_1803_ = lean_string_utf8_extract(v_str_1800_, v_startPos_1801_, v_stopPos_1802_);
lean_inc(v_info_1799_);
v___x_1804_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1799_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v_s_1805_ = lean_string_append(v_b_1767_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v_a_1785_ = v_s_1805_;
goto v___jp_1784_;
}
case 1:
{
lean_object* v_kind_1806_; lean_object* v_args_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_kind_1806_ = lean_ctor_get(v_stx_1766_, 1);
v_args_1807_ = lean_ctor_get(v_stx_1766_, 2);
v___x_1808_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1809_ = lean_name_eq(v_kind_1806_, v___x_1808_);
if (v___x_1809_ == 0)
{
v_a_1785_ = v_b_1767_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = lean_array_get_borrowed(v___x_1783_, v_args_1807_, v___x_1810_);
lean_inc(v___x_1811_);
v___x_1812_ = l_Lean_Syntax_reprint(v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; 
lean_dec_ref_known(v_stx_1766_, 3);
lean_dec_ref(v_b_1767_);
v___x_1813_ = lean_box(0);
return v___x_1813_;
}
else
{
lean_object* v_val_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_val_1814_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = lean_array_get_size(v_args_1807_);
lean_inc_ref(v_args_1807_);
v___x_1817_ = l_Array_toSubarray___redArg(v_args_1807_, v___x_1815_, v___x_1816_);
v___x_1818_ = lean_box(0);
v___x_1819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1814_, v___x_1817_, v___x_1818_);
lean_dec(v_val_1814_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1820_; 
lean_dec_ref_known(v_stx_1766_, 3);
lean_dec_ref(v_b_1767_);
v___x_1820_ = lean_box(0);
return v___x_1820_;
}
else
{
lean_dec_ref_known(v___x_1819_, 1);
v_a_1785_ = v_b_1767_;
goto v___jp_1784_;
}
}
}
}
default: 
{
v_a_1785_ = v_b_1767_;
goto v___jp_1784_;
}
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_b_1769_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
v___jp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___y_1773_);
v_sz_1777_ = lean_array_size(v___y_1774_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1765_, v___y_1774_, v_sz_1777_, v___x_1778_, v___x_1776_);
lean_dec_ref(v___y_1774_);
if (lean_obj_tag(v___x_1779_) == 0)
{
return v___x_1775_;
}
else
{
lean_object* v_val_1780_; lean_object* v_fst_1781_; 
v_val_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v_fst_1781_ = lean_ctor_get(v_val_1780_, 0);
if (lean_obj_tag(v_fst_1781_) == 0)
{
lean_object* v_snd_1782_; 
v_snd_1782_ = lean_ctor_get(v_val_1780_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_val_1780_);
v_b_1769_ = v_snd_1782_;
goto v___jp_1768_;
}
else
{
lean_inc_ref(v_fst_1781_);
lean_dec(v_val_1780_);
return v_fst_1781_;
}
}
}
v___jp_1784_:
{
if (lean_obj_tag(v_stx_1766_) == 1)
{
if (v_firstChoiceOnly_1765_ == 0)
{
lean_object* v_args_1786_; 
v_args_1786_ = lean_ctor_get(v_stx_1766_, 2);
lean_inc_ref(v_args_1786_);
lean_dec_ref_known(v_stx_1766_, 3);
v___y_1773_ = v_a_1785_;
v___y_1774_ = v_args_1786_;
goto v___jp_1772_;
}
else
{
lean_object* v_kind_1787_; lean_object* v_args_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_kind_1787_ = lean_ctor_get(v_stx_1766_, 1);
lean_inc(v_kind_1787_);
v_args_1788_ = lean_ctor_get(v_stx_1766_, 2);
lean_inc_ref(v_args_1788_);
lean_dec_ref_known(v_stx_1766_, 3);
v___x_1789_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1790_ = lean_name_eq(v_kind_1787_, v___x_1789_);
lean_dec(v_kind_1787_);
if (v___x_1790_ == 0)
{
v___y_1773_ = v_a_1785_;
v___y_1774_ = v_args_1788_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_array_get(v___x_1783_, v_args_1788_, v___x_1791_);
lean_dec_ref(v_args_1788_);
v_stx_1766_ = v___x_1792_;
v_b_1767_ = v_a_1785_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1766_);
v_b_1769_ = v_a_1785_;
goto v___jp_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1821_){
_start:
{
lean_object* v_s_1822_; uint8_t v___x_1823_; lean_object* v___x_1824_; 
v_s_1822_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1823_ = 1;
v___x_1824_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1823_, v_stx_1821_, v_s_1822_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_box(0);
return v___x_1825_;
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1834_; 
v_val_1826_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1828_ = v___x_1824_;
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_val_1826_);
lean_dec(v___x_1824_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_a_1830_; lean_object* v___x_1832_; 
v_a_1830_ = lean_ctor_get(v_val_1826_, 0);
lean_inc(v_a_1830_);
lean_dec(v_val_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v_a_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1835_, lean_object* v_a_1836_, lean_object* v_b_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1835_, v_a_1836_, v_b_1837_);
lean_dec_ref(v_val_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1839_, lean_object* v_as_1840_, lean_object* v_sz_1841_, lean_object* v_i_1842_, lean_object* v_b_1843_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1844_; size_t v_sz_boxed_1845_; size_t v_i_boxed_1846_; lean_object* v_res_1847_; 
v_firstChoiceOnly_boxed_1844_ = lean_unbox(v_firstChoiceOnly_1839_);
v_sz_boxed_1845_ = lean_unbox_usize(v_sz_1841_);
lean_dec(v_sz_1841_);
v_i_boxed_1846_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1844_, v_as_1840_, v_sz_boxed_1845_, v_i_boxed_1846_, v_b_1843_);
lean_dec_ref(v_as_1840_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1848_, lean_object* v_stx_1849_, lean_object* v_b_1850_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1851_; lean_object* v_res_1852_; 
v_firstChoiceOnly_boxed_1851_ = lean_unbox(v_firstChoiceOnly_1848_);
v_res_1852_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1851_, v_stx_1849_, v_b_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1853_, lean_object* v_inst_1854_, lean_object* v_R_1855_, lean_object* v_a_1856_, lean_object* v_b_1857_, lean_object* v_c_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1853_, v_a_1856_, v_b_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1860_, lean_object* v_inst_1861_, lean_object* v_R_1862_, lean_object* v_a_1863_, lean_object* v_b_1864_, lean_object* v_c_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1860_, v_inst_1861_, v_R_1862_, v_a_1863_, v_b_1864_, v_c_1865_);
lean_dec_ref(v_val_1860_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1875_, lean_object* v_stx_1876_){
_start:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Lean_Syntax_isMissing(v_stx_1876_);
if (v___x_1878_ == 0)
{
if (lean_obj_tag(v_stx_1876_) == 1)
{
lean_object* v_kind_1879_; lean_object* v_args_1880_; 
v_kind_1879_ = lean_ctor_get(v_stx_1876_, 1);
v_args_1880_ = lean_ctor_get(v_stx_1876_, 2);
if (v_firstChoiceOnly_1875_ == 0)
{
goto v___jp_1881_;
}
else
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1891_ = lean_name_eq(v_kind_1879_, v___x_1890_);
if (v___x_1891_ == 0)
{
goto v___jp_1881_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_array_get_borrowed(v___x_1892_, v_args_1880_, v___x_1893_);
v_stx_1876_ = v___x_1894_;
goto _start;
}
}
v___jp_1881_:
{
lean_object* v___x_1882_; size_t v_sz_1883_; size_t v___x_1884_; lean_object* v___x_1885_; lean_object* v_fst_1886_; 
v___x_1882_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1883_ = lean_array_size(v_args_1880_);
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1875_, v_args_1880_, v_sz_1883_, v___x_1884_, v___x_1882_);
v_fst_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_fst_1886_);
if (lean_obj_tag(v_fst_1886_) == 0)
{
lean_object* v_snd_1887_; lean_object* v___x_1888_; 
v_snd_1887_ = lean_ctor_get(v___x_1885_, 1);
lean_inc(v_snd_1887_);
lean_dec_ref(v___x_1885_);
v___x_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_snd_1887_);
return v___x_1888_;
}
else
{
lean_object* v_val_1889_; 
lean_dec_ref(v___x_1885_);
v_val_1889_ = lean_ctor_get(v_fst_1886_, 0);
lean_inc(v_val_1889_);
lean_dec_ref_known(v_fst_1886_, 1);
return v_val_1889_;
}
}
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1896_;
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_box(v___x_1878_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___x_1877_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1901_, lean_object* v_as_1902_, size_t v_sz_1903_, size_t v_i_1904_, lean_object* v_b_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_lt(v_i_1904_, v_sz_1903_);
if (v___x_1906_ == 0)
{
return v_b_1905_;
}
else
{
lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1925_; 
v_snd_1907_ = lean_ctor_get(v_b_1905_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_b_1905_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v_b_1905_, 0);
lean_dec(v_unused_1926_);
v___x_1909_ = v_b_1905_;
v_isShared_1910_ = v_isSharedCheck_1925_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_dec(v_b_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1925_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_array_uget_borrowed(v_as_1902_, v_i_1904_);
v___x_1912_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1901_, v_a_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1913_);
v___x_1915_ = v___x_1909_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_snd_1907_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_dec(v_snd_1907_);
v_a_1917_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1918_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v_a_1917_);
lean_ctor_set(v___x_1909_, 0, v___x_1918_);
v___x_1920_ = v___x_1909_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_a_1917_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1904_, v___x_1921_);
v_i_1904_ = v___x_1922_;
v_b_1905_ = v___x_1920_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1927_, lean_object* v_as_1928_, lean_object* v_sz_1929_, lean_object* v_i_1930_, lean_object* v_b_1931_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1932_; size_t v_sz_boxed_1933_; size_t v_i_boxed_1934_; lean_object* v_res_1935_; 
v_firstChoiceOnly_boxed_1932_ = lean_unbox(v_firstChoiceOnly_1927_);
v_sz_boxed_1933_ = lean_unbox_usize(v_sz_1929_);
lean_dec(v_sz_1929_);
v_i_boxed_1934_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1932_, v_as_1928_, v_sz_boxed_1933_, v_i_boxed_1934_, v_b_1931_);
lean_dec_ref(v_as_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1936_, lean_object* v_stx_1937_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1938_; lean_object* v_res_1939_; 
v_firstChoiceOnly_boxed_1938_ = lean_unbox(v_firstChoiceOnly_1936_);
v_res_1939_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1938_, v_stx_1937_);
lean_dec(v_stx_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1940_){
_start:
{
uint8_t v___x_1941_; lean_object* v___y_1943_; lean_object* v___x_1947_; lean_object* v_a_1948_; 
v___x_1941_ = 0;
v___x_1947_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1941_, v_stx_1940_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___y_1943_ = v_a_1948_;
goto v___jp_1942_;
v___jp_1942_:
{
lean_object* v_fst_1944_; 
v_fst_1944_ = lean_ctor_get(v___y_1943_, 0);
lean_inc(v_fst_1944_);
lean_dec_ref(v___y_1943_);
if (lean_obj_tag(v_fst_1944_) == 0)
{
return v___x_1941_;
}
else
{
lean_object* v_val_1945_; uint8_t v___x_1946_; 
v_val_1945_ = lean_ctor_get(v_fst_1944_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v_fst_1944_, 1);
v___x_1946_ = lean_unbox(v_val_1945_);
lean_dec(v_val_1945_);
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1949_){
_start:
{
uint8_t v_res_1950_; lean_object* v_r_1951_; 
v_res_1950_ = l_Lean_Syntax_hasMissing(v_stx_1949_);
lean_dec(v_stx_1949_);
v_r_1951_ = lean_box(v_res_1950_);
return v_r_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1952_, lean_object* v_stx_1953_, lean_object* v_b_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1952_, v_stx_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1956_, lean_object* v_stx_1957_, lean_object* v_b_1958_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1959_; lean_object* v_res_1960_; 
v_firstChoiceOnly_boxed_1959_ = lean_unbox(v_firstChoiceOnly_1956_);
v_res_1960_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1959_, v_stx_1957_, v_b_1958_);
lean_dec_ref(v_b_1958_);
lean_dec(v_stx_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1961_, uint8_t v_canonicalOnly_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_Syntax_getPos_x3f(v_stx_1961_, v_canonicalOnly_1962_);
if (lean_obj_tag(v___x_1963_) == 1)
{
lean_object* v_val_1964_; lean_object* v___x_1965_; 
v_val_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1961_, v_canonicalOnly_1962_);
if (lean_obj_tag(v___x_1965_) == 1)
{
lean_object* v_val_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_val_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_val_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_val_1964_);
lean_ctor_set(v___x_1970_, 1, v_val_1966_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v___x_1975_; 
lean_dec(v___x_1965_);
lean_dec(v_val_1964_);
v___x_1975_ = lean_box(0);
return v___x_1975_;
}
}
else
{
lean_object* v___x_1976_; 
lean_dec(v___x_1963_);
v___x_1976_ = lean_box(0);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1977_, lean_object* v_canonicalOnly_1978_){
_start:
{
uint8_t v_canonicalOnly_boxed_1979_; lean_object* v_res_1980_; 
v_canonicalOnly_boxed_1979_ = lean_unbox(v_canonicalOnly_1978_);
v_res_1980_ = l_Lean_Syntax_getRange_x3f(v_stx_1977_, v_canonicalOnly_boxed_1979_);
lean_dec(v_stx_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1981_, uint8_t v_canonicalOnly_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Syntax_getPos_x3f(v_stx_1981_, v_canonicalOnly_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
else
{
lean_object* v_val_1985_; lean_object* v___x_1986_; 
v_val_1985_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1986_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1981_, v_canonicalOnly_1982_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; 
lean_dec(v_val_1985_);
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_val_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_val_1985_);
lean_ctor_set(v___x_1992_, 1, v_val_1988_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1997_, lean_object* v_canonicalOnly_1998_){
_start:
{
uint8_t v_canonicalOnly_boxed_1999_; lean_object* v_res_2000_; 
v_canonicalOnly_boxed_1999_ = lean_unbox(v_canonicalOnly_1998_);
v_res_2000_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1997_, v_canonicalOnly_boxed_1999_);
lean_dec(v_stx_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_2001_, uint8_t v_canonical_2002_){
_start:
{
lean_object* v_start_2003_; lean_object* v_stop_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2013_; 
v_start_2003_ = lean_ctor_get(v_range_2001_, 0);
v_stop_2004_ = lean_ctor_get(v_range_2001_, 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_range_2001_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2006_ = v_range_2001_;
v_isShared_2007_ = v_isSharedCheck_2013_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_stop_2004_);
lean_inc(v_start_2003_);
lean_dec(v_range_2001_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2013_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2008_, 0, v_start_2003_);
lean_ctor_set(v___x_2008_, 1, v_stop_2004_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*2, v_canonical_2002_);
v___x_2009_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 2);
lean_ctor_set(v___x_2006_, 1, v___x_2009_);
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2011_ = v___x_2006_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2014_, lean_object* v_canonical_2015_){
_start:
{
uint8_t v_canonical_boxed_2016_; lean_object* v_res_2017_; 
v_canonical_boxed_2016_ = lean_unbox(v_canonical_2015_);
v_res_2017_ = l_Lean_Syntax_ofRange(v_range_2014_, v_canonical_boxed_2016_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2020_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2022_, 0, v_stx_2020_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_ctor_set(v___x_2022_, 2, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2023_, lean_object* v_stx_2024_){
_start:
{
lean_object* v_parents_2025_; lean_object* v_idxs_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_parents_2025_ = lean_ctor_get(v_t_2023_, 1);
v_idxs_2026_ = lean_ctor_get(v_t_2023_, 2);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_t_2023_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v_t_2023_, 0);
lean_dec(v_unused_2034_);
v___x_2028_ = v_t_2023_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_idxs_2026_);
lean_inc(v_parents_2025_);
lean_dec(v_t_2023_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v_stx_2024_);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_stx_2024_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_parents_2025_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_idxs_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2035_, lean_object* v_idx_2036_){
_start:
{
lean_object* v_cur_2037_; lean_object* v_parents_2038_; lean_object* v_idxs_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2059_; 
v_cur_2037_ = lean_ctor_get(v_t_2035_, 0);
v_parents_2038_ = lean_ctor_get(v_t_2035_, 1);
v_idxs_2039_ = lean_ctor_get(v_t_2035_, 2);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_t_2035_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2041_ = v_t_2035_;
v_isShared_2042_ = v_isSharedCheck_2059_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_idxs_2039_);
lean_inc(v_parents_2038_);
lean_inc(v_cur_2037_);
lean_dec(v_t_2035_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2059_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = l_Lean_Syntax_getNumArgs(v_cur_2037_);
v___x_2044_ = lean_nat_dec_lt(v_idx_2036_, v___x_2043_);
lean_dec(v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_array_push(v_parents_2038_, v_cur_2037_);
v___x_2047_ = lean_array_push(v_idxs_2039_, v_idx_2036_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 2, v___x_2047_);
lean_ctor_set(v___x_2041_, 1, v___x_2046_);
lean_ctor_set(v___x_2041_, 0, v___x_2045_);
v___x_2049_ = v___x_2041_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2051_ = l_Lean_Syntax_getArg(v_cur_2037_, v_idx_2036_);
v___x_2052_ = lean_box(0);
v___x_2053_ = l_Lean_Syntax_setArg(v_cur_2037_, v_idx_2036_, v___x_2052_);
v___x_2054_ = lean_array_push(v_parents_2038_, v___x_2053_);
v___x_2055_ = lean_array_push(v_idxs_2039_, v_idx_2036_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 2, v___x_2055_);
lean_ctor_set(v___x_2041_, 1, v___x_2054_);
lean_ctor_set(v___x_2041_, 0, v___x_2051_);
v___x_2057_ = v___x_2041_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2060_){
_start:
{
lean_object* v_cur_2061_; lean_object* v_parents_2062_; lean_object* v_idxs_2063_; lean_object* v___y_2065_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_cur_2061_ = lean_ctor_get(v_t_2060_, 0);
v_parents_2062_ = lean_ctor_get(v_t_2060_, 1);
v_idxs_2063_ = lean_ctor_get(v_t_2060_, 2);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_array_get_size(v_parents_2062_);
v___x_2071_ = lean_nat_dec_lt(v___x_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
return v_t_2060_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
lean_inc_ref(v_idxs_2063_);
lean_inc_ref(v_parents_2062_);
lean_inc(v_cur_2061_);
lean_dec_ref(v_t_2060_);
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_array_get_size(v_idxs_2063_);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_sub(v___x_2073_, v___x_2074_);
v___x_2076_ = lean_array_get_borrowed(v___x_2069_, v_idxs_2063_, v___x_2075_);
lean_dec(v___x_2075_);
v___x_2077_ = lean_nat_sub(v___x_2070_, v___x_2074_);
v___x_2078_ = lean_array_get_borrowed(v___x_2072_, v_parents_2062_, v___x_2077_);
lean_dec(v___x_2077_);
v___x_2079_ = l_Lean_Syntax_getNumArgs(v___x_2078_);
v___x_2080_ = lean_nat_dec_lt(v___x_2076_, v___x_2079_);
lean_dec(v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v_cur_2061_);
lean_inc(v___x_2078_);
v___y_2065_ = v___x_2078_;
goto v___jp_2064_;
}
else
{
lean_object* v___x_2081_; 
lean_inc(v___x_2078_);
v___x_2081_ = l_Lean_Syntax_setArg(v___x_2078_, v___x_2076_, v_cur_2061_);
v___y_2065_ = v___x_2081_;
goto v___jp_2064_;
}
}
v___jp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_array_pop(v_parents_2062_);
v___x_2067_ = lean_array_pop(v_idxs_2063_);
v___x_2068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2068_, 0, v___y_2065_);
lean_ctor_set(v___x_2068_, 1, v___x_2066_);
lean_ctor_set(v___x_2068_, 2, v___x_2067_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2082_){
_start:
{
lean_object* v_parents_2083_; lean_object* v_idxs_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_parents_2083_ = lean_ctor_get(v_t_2082_, 1);
v_idxs_2084_ = lean_ctor_get(v_t_2082_, 2);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_array_get_size(v_parents_2083_);
v___x_2087_ = lean_nat_dec_lt(v___x_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
return v_t_2082_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_inc_ref(v_idxs_2084_);
v___x_2088_ = l_Lean_Syntax_Traverser_up(v_t_2082_);
v___x_2089_ = lean_array_get_size(v_idxs_2084_);
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_nat_sub(v___x_2089_, v___x_2090_);
v___x_2092_ = lean_array_get(v___x_2085_, v_idxs_2084_, v___x_2091_);
lean_dec(v___x_2091_);
lean_dec_ref(v_idxs_2084_);
v___x_2093_ = lean_nat_sub(v___x_2092_, v___x_2090_);
lean_dec(v___x_2092_);
v___x_2094_ = l_Lean_Syntax_Traverser_down(v___x_2088_, v___x_2093_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2095_){
_start:
{
lean_object* v_parents_2096_; lean_object* v_idxs_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_parents_2096_ = lean_ctor_get(v_t_2095_, 1);
v_idxs_2097_ = lean_ctor_get(v_t_2095_, 2);
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = lean_array_get_size(v_parents_2096_);
v___x_2100_ = lean_nat_dec_lt(v___x_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
return v_t_2095_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_inc_ref(v_idxs_2097_);
v___x_2101_ = l_Lean_Syntax_Traverser_up(v_t_2095_);
v___x_2102_ = lean_array_get_size(v_idxs_2097_);
v___x_2103_ = lean_unsigned_to_nat(1u);
v___x_2104_ = lean_nat_sub(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_array_get(v___x_2098_, v_idxs_2097_, v___x_2104_);
lean_dec(v___x_2104_);
lean_dec_ref(v_idxs_2097_);
v___x_2106_ = lean_nat_add(v___x_2105_, v___x_2103_);
lean_dec(v___x_2105_);
v___x_2107_ = l_Lean_Syntax_Traverser_down(v___x_2101_, v___x_2106_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2108_){
_start:
{
lean_object* v_cur_2109_; 
v_cur_2109_ = lean_ctor_get(v_self_2108_, 0);
lean_inc(v_cur_2109_);
return v_cur_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2110_);
lean_dec_ref(v_self_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2113_, lean_object* v_t_2114_){
_start:
{
lean_object* v_toApplicative_2115_; lean_object* v_toFunctor_2116_; lean_object* v_map_2117_; lean_object* v_get_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; 
v_toApplicative_2115_ = lean_ctor_get(v_inst_2113_, 0);
lean_inc_ref(v_toApplicative_2115_);
lean_dec_ref(v_inst_2113_);
v_toFunctor_2116_ = lean_ctor_get(v_toApplicative_2115_, 0);
lean_inc_ref(v_toFunctor_2116_);
lean_dec_ref(v_toApplicative_2115_);
v_map_2117_ = lean_ctor_get(v_toFunctor_2116_, 0);
lean_inc(v_map_2117_);
lean_dec_ref(v_toFunctor_2116_);
v_get_2118_ = lean_ctor_get(v_t_2114_, 0);
lean_inc(v_get_2118_);
lean_dec_ref(v_t_2114_);
v___f_2119_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2120_ = lean_apply_4(v_map_2117_, lean_box(0), lean_box(0), v___f_2119_, v_get_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2121_, lean_object* v_inst_2122_, lean_object* v_t_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2122_, v_t_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2125_, lean_object* v_s_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
v___x_2128_ = l_Lean_Syntax_Traverser_setCur(v_s_2126_, v_stx_2125_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2130_, lean_object* v_stx_2131_){
_start:
{
lean_object* v_modifyGet_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; 
v_modifyGet_2132_ = lean_ctor_get(v_t_2130_, 2);
lean_inc(v_modifyGet_2132_);
lean_dec_ref(v_t_2130_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2133_, 0, v_stx_2131_);
v___x_2134_ = lean_apply_2(v_modifyGet_2132_, lean_box(0), v___f_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2135_, lean_object* v_t_2136_, lean_object* v_stx_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2136_, v_stx_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2139_, lean_object* v_s_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = l_Lean_Syntax_Traverser_down(v_s_2140_, v_idx_2139_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2144_, lean_object* v_idx_2145_){
_start:
{
lean_object* v_modifyGet_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; 
v_modifyGet_2146_ = lean_ctor_get(v_t_2144_, 2);
lean_inc(v_modifyGet_2146_);
lean_dec_ref(v_t_2144_);
v___f_2147_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2147_, 0, v_idx_2145_);
v___x_2148_ = lean_apply_2(v_modifyGet_2146_, lean_box(0), v___f_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2149_, lean_object* v_t_2150_, lean_object* v_idx_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2150_, v_idx_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Lean_Syntax_Traverser_up(v_s_2153_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2158_){
_start:
{
lean_object* v_modifyGet_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; 
v_modifyGet_2159_ = lean_ctor_get(v_t_2158_, 2);
lean_inc(v_modifyGet_2159_);
lean_dec_ref(v_t_2158_);
v___f_2160_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2161_ = lean_apply_2(v_modifyGet_2159_, lean_box(0), v___f_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2162_, lean_object* v_t_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = l_Lean_Syntax_Traverser_left(v_s_2165_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2170_){
_start:
{
lean_object* v_modifyGet_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; 
v_modifyGet_2171_ = lean_ctor_get(v_t_2170_, 2);
lean_inc(v_modifyGet_2171_);
lean_dec_ref(v_t_2170_);
v___f_2172_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2173_ = lean_apply_2(v_modifyGet_2171_, lean_box(0), v___f_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2174_, lean_object* v_t_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = l_Lean_Syntax_Traverser_right(v_s_2177_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2182_){
_start:
{
lean_object* v_modifyGet_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; 
v_modifyGet_2183_ = lean_ctor_get(v_t_2182_, 2);
lean_inc(v_modifyGet_2183_);
lean_dec_ref(v_t_2182_);
v___f_2184_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2185_ = lean_apply_2(v_modifyGet_2183_, lean_box(0), v___f_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2186_, lean_object* v_t_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2189_, lean_object* v_st_2190_){
_start:
{
lean_object* v_idxs_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_idxs_2191_ = lean_ctor_get(v_st_2190_, 2);
v___x_2192_ = lean_array_get_size(v_idxs_2191_);
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = lean_nat_sub(v___x_2192_, v___x_2193_);
v___x_2195_ = lean_nat_dec_lt(v___x_2194_, v___x_2192_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v___x_2194_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_apply_2(v_toPure_2189_, lean_box(0), v___x_2196_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_array_fget_borrowed(v_idxs_2191_, v___x_2194_);
lean_dec(v___x_2194_);
lean_inc(v___x_2198_);
v___x_2199_ = lean_apply_2(v_toPure_2189_, lean_box(0), v___x_2198_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2200_, lean_object* v_st_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2200_, v_st_2201_);
lean_dec_ref(v_st_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2203_, lean_object* v_t_2204_){
_start:
{
lean_object* v_toApplicative_2205_; lean_object* v_toBind_2206_; lean_object* v_get_2207_; lean_object* v_toPure_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; 
v_toApplicative_2205_ = lean_ctor_get(v_inst_2203_, 0);
lean_inc_ref(v_toApplicative_2205_);
v_toBind_2206_ = lean_ctor_get(v_inst_2203_, 1);
lean_inc(v_toBind_2206_);
lean_dec_ref(v_inst_2203_);
v_get_2207_ = lean_ctor_get(v_t_2204_, 0);
lean_inc(v_get_2207_);
lean_dec_ref(v_t_2204_);
v_toPure_2208_ = lean_ctor_get(v_toApplicative_2205_, 1);
lean_inc(v_toPure_2208_);
lean_dec_ref(v_toApplicative_2205_);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2209_, 0, v_toPure_2208_);
v___x_2210_ = lean_apply_4(v_toBind_2206_, lean_box(0), lean_box(0), v_get_2207_, v___f_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2211_, lean_object* v_inst_2212_, lean_object* v_t_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2212_, v_t_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2215_, lean_object* v_i_2216_){
_start:
{
lean_object* v_args_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v_args_2217_ = lean_ctor_get(v_n_2215_, 2);
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_array_get_borrowed(v___x_2218_, v_args_2217_, v_i_2216_);
v___x_2220_ = l_Lean_Syntax_getId(v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2221_, lean_object* v_i_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_SyntaxNode_getIdAt(v_n_2221_, v_i_2222_);
lean_dec(v_i_2222_);
lean_dec(v_n_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2226_ = lean_box(2);
v___x_2227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2225_);
lean_ctor_set(v___x_2227_, 2, v_args_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2233_){
_start:
{
if (lean_obj_tag(v_x_2233_) == 1)
{
lean_object* v_kind_2234_; 
v_kind_2234_ = lean_ctor_get(v_x_2233_, 1);
if (lean_obj_tag(v_kind_2234_) == 1)
{
lean_object* v_pre_2235_; lean_object* v_str_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_pre_2235_ = lean_ctor_get(v_kind_2234_, 0);
v_str_2236_ = lean_ctor_get(v_kind_2234_, 1);
v___x_2237_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2238_ = lean_string_dec_eq(v_str_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2240_ = lean_string_dec_eq(v_str_2236_, v___x_2239_);
if (v___x_2240_ == 0)
{
return v___x_2240_;
}
else
{
if (lean_obj_tag(v_pre_2235_) == 1)
{
lean_object* v_pre_2241_; 
v_pre_2241_ = lean_ctor_get(v_pre_2235_, 0);
if (lean_obj_tag(v_pre_2241_) == 1)
{
lean_object* v_pre_2242_; 
v_pre_2242_ = lean_ctor_get(v_pre_2241_, 0);
if (lean_obj_tag(v_pre_2242_) == 1)
{
lean_object* v_pre_2243_; 
v_pre_2243_ = lean_ctor_get(v_pre_2242_, 0);
if (lean_obj_tag(v_pre_2243_) == 0)
{
lean_object* v_str_2244_; lean_object* v_str_2245_; lean_object* v_str_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_str_2244_ = lean_ctor_get(v_pre_2235_, 1);
v_str_2245_ = lean_ctor_get(v_pre_2241_, 1);
v_str_2246_ = lean_ctor_get(v_pre_2242_, 1);
v___x_2247_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2248_ = lean_string_dec_eq(v_str_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
return v___x_2238_;
}
else
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2250_ = lean_string_dec_eq(v_str_2245_, v___x_2249_);
if (v___x_2250_ == 0)
{
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2252_ = lean_string_dec_eq(v_str_2244_, v___x_2251_);
return v___x_2252_;
}
}
}
else
{
return v___x_2238_;
}
}
else
{
return v___x_2238_;
}
}
else
{
return v___x_2238_;
}
}
else
{
return v___x_2238_;
}
}
}
else
{
return v___x_2238_;
}
}
else
{
uint8_t v___x_2253_; 
v___x_2253_ = 0;
return v___x_2253_;
}
}
else
{
uint8_t v___x_2254_; 
v___x_2254_ = 0;
return v___x_2254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2255_){
_start:
{
uint8_t v_res_2256_; lean_object* v_r_2257_; 
v_res_2256_ = l_Lean_Syntax_isQuot(v_x_2255_);
lean_dec(v_x_2255_);
v_r_2257_ = lean_box(v_res_2256_);
return v_r_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___y_2267_; uint8_t v___x_2273_; 
v___x_2264_ = l_Lean_Syntax_getNumArgs(v_stx_2263_);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_dec_eq(v___x_2264_, v___x_2265_);
lean_dec(v___x_2264_);
if (v___x_2273_ == 0)
{
v___y_2267_ = v_stx_2263_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = l_Lean_Syntax_getArg(v_stx_2263_, v___x_2274_);
lean_dec(v_stx_2263_);
v___y_2267_ = v___x_2275_;
goto v___jp_2266_;
}
v___jp_2266_:
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2267_);
v___x_2269_ = l_Lean_Syntax_isOfKind(v___y_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Syntax_getArg(v___y_2267_, v___x_2265_);
lean_dec(v___y_2267_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(3u);
v___x_2272_ = l_Lean_Syntax_getArg(v___y_2267_, v___x_2271_);
lean_dec(v___y_2267_);
return v___x_2272_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2277_) == 1)
{
lean_object* v_kind_2278_; 
v_kind_2278_ = lean_ctor_get(v_x_2277_, 1);
if (lean_obj_tag(v_kind_2278_) == 1)
{
lean_object* v_str_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_str_2279_ = lean_ctor_get(v_kind_2278_, 1);
v___x_2280_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2281_ = lean_string_dec_eq(v_str_2279_, v___x_2280_);
return v___x_2281_;
}
else
{
uint8_t v___x_2282_; 
v___x_2282_ = 0;
return v___x_2282_;
}
}
else
{
uint8_t v___x_2283_; 
v___x_2283_ = 0;
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2284_){
_start:
{
uint8_t v_res_2285_; lean_object* v_r_2286_; 
v_res_2285_ = l_Lean_Syntax_isAntiquot(v_x_2284_);
lean_dec(v_x_2284_);
v_r_2286_ = lean_box(v_res_2285_);
return v_r_2286_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2287_, uint8_t v___x_2288_, lean_object* v_as_2289_, size_t v_i_2290_, size_t v_stop_2291_){
_start:
{
uint8_t v___x_2292_; 
v___x_2292_ = lean_usize_dec_eq(v_i_2290_, v_stop_2291_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; uint8_t v___y_2295_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2293_ = 1;
v___x_2299_ = lean_array_uget_borrowed(v_as_2289_, v_i_2290_);
v___x_2300_ = l_Lean_Syntax_isAntiquot(v___x_2299_);
if (v___x_2300_ == 0)
{
v___y_2295_ = v___y_2287_;
goto v___jp_2294_;
}
else
{
v___y_2295_ = v___x_2288_;
goto v___jp_2294_;
}
v___jp_2294_:
{
if (v___y_2295_ == 0)
{
size_t v___x_2296_; size_t v___x_2297_; 
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2290_, v___x_2296_);
v_i_2290_ = v___x_2297_;
goto _start;
}
else
{
return v___x_2293_;
}
}
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = 0;
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2302_, lean_object* v___x_2303_, lean_object* v_as_2304_, lean_object* v_i_2305_, lean_object* v_stop_2306_){
_start:
{
uint8_t v___y_330__boxed_2307_; uint8_t v___x_331__boxed_2308_; size_t v_i_boxed_2309_; size_t v_stop_boxed_2310_; uint8_t v_res_2311_; lean_object* v_r_2312_; 
v___y_330__boxed_2307_ = lean_unbox(v___y_2302_);
v___x_331__boxed_2308_ = lean_unbox(v___x_2303_);
v_i_boxed_2309_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_stop_boxed_2310_ = lean_unbox_usize(v_stop_2306_);
lean_dec(v_stop_2306_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_330__boxed_2307_, v___x_331__boxed_2308_, v_as_2304_, v_i_boxed_2309_, v_stop_boxed_2310_);
lean_dec_ref(v_as_2304_);
v_r_2312_ = lean_box(v_res_2311_);
return v_r_2312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2313_){
_start:
{
uint8_t v___x_2314_; uint8_t v___y_2316_; 
v___x_2314_ = l_Lean_Syntax_isAntiquot(v_stx_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2313_);
v___x_2325_ = l_Lean_Syntax_isOfKind(v_stx_2313_, v___x_2324_);
if (v___x_2325_ == 0)
{
v___y_2316_ = v___x_2325_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = l_Lean_Syntax_getNumArgs(v_stx_2313_);
v___x_2328_ = lean_nat_dec_lt(v___x_2326_, v___x_2327_);
lean_dec(v___x_2327_);
v___y_2316_ = v___x_2328_;
goto v___jp_2315_;
}
}
else
{
lean_dec(v_stx_2313_);
return v___x_2314_;
}
v___jp_2315_:
{
if (v___y_2316_ == 0)
{
lean_dec(v_stx_2313_);
return v___y_2316_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2317_ = l_Lean_Syntax_getArgs(v_stx_2313_);
lean_dec(v_stx_2313_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_array_get_size(v___x_2317_);
v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec_ref(v___x_2317_);
return v___y_2316_;
}
else
{
if (v___x_2320_ == 0)
{
lean_dec_ref(v___x_2317_);
return v___y_2316_;
}
else
{
size_t v___x_2321_; size_t v___x_2322_; uint8_t v___x_2323_; 
v___x_2321_ = ((size_t)0ULL);
v___x_2322_ = lean_usize_of_nat(v___x_2319_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2316_, v___x_2314_, v___x_2317_, v___x_2321_, v___x_2322_);
lean_dec_ref(v___x_2317_);
if (v___x_2323_ == 0)
{
return v___x_2320_;
}
else
{
return v___x_2314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2329_){
_start:
{
uint8_t v_res_2330_; lean_object* v_r_2331_; 
v_res_2330_ = l_Lean_Syntax_isAntiquots(v_stx_2329_);
v_r_2331_ = lean_box(v_res_2330_);
return v_r_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2332_){
_start:
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2332_);
v___x_2334_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
return v_stx_2332_;
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2335_);
lean_dec(v_stx_2332_);
return v___x_2336_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2339_ = l_Lean_mkAtom(v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2342_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2343_ = lean_unsigned_to_nat(4u);
v___x_2344_ = lean_mk_empty_array_with_capacity(v___x_2343_);
v___x_2345_ = lean_array_push(v___x_2344_, v___x_2342_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2354_ = l_Lean_mkAtom(v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2355_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2356_ = lean_unsigned_to_nat(2u);
v___x_2357_ = lean_mk_empty_array_with_capacity(v___x_2356_);
v___x_2358_ = lean_array_push(v___x_2357_, v___x_2355_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2370_ = l_Lean_mkAtom(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2373_ = l_Lean_mkAtom(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2374_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2375_ = lean_unsigned_to_nat(3u);
v___x_2376_ = lean_mk_empty_array_with_capacity(v___x_2375_);
v___x_2377_ = lean_array_push(v___x_2376_, v___x_2374_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2378_, lean_object* v_term_2379_, lean_object* v_nesting_2380_, lean_object* v_name_2381_, uint8_t v_isPseudoKind_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_nesting_2387_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2406_; uint8_t v___x_2414_; 
v___x_2383_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2384_ = lean_mk_array(v_nesting_2380_, v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2386_ = lean_box(2);
v_nesting_2387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2387_, 0, v___x_2386_);
lean_ctor_set(v_nesting_2387_, 1, v___x_2385_);
lean_ctor_set(v_nesting_2387_, 2, v___x_2384_);
v___x_2414_ = l_Lean_Syntax_isIdent(v_term_2379_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2379_);
v___x_2416_ = l_Lean_Syntax_isOfKind(v_term_2379_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2417_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2418_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2419_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2420_ = lean_array_push(v___x_2419_, v_term_2379_);
v___x_2421_ = lean_array_push(v___x_2420_, v___x_2418_);
v___x_2422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2386_);
lean_ctor_set(v___x_2422_, 1, v___x_2417_);
lean_ctor_set(v___x_2422_, 2, v___x_2421_);
v___y_2406_ = v___x_2422_;
goto v___jp_2405_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = l_Lean_Syntax_getArg(v_term_2379_, v___x_2423_);
lean_dec(v_term_2379_);
v___y_2406_ = v___x_2424_;
goto v___jp_2405_;
}
}
else
{
v___y_2406_ = v_term_2379_;
goto v___jp_2405_;
}
v___jp_2388_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_inc(v___y_2391_);
v___x_2392_ = l_Lean_Name_append(v_kind_2378_, v___y_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2394_ = l_Lean_Name_append(v___x_2392_, v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2396_ = lean_array_push(v___x_2395_, v_nesting_2387_);
v___x_2397_ = lean_array_push(v___x_2396_, v___y_2390_);
v___x_2398_ = lean_array_push(v___x_2397_, v___y_2389_);
v___x_2399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2386_);
lean_ctor_set(v___x_2399_, 1, v___x_2394_);
lean_ctor_set(v___x_2399_, 2, v___x_2398_);
return v___x_2399_;
}
v___jp_2400_:
{
if (v_isPseudoKind_2382_ == 0)
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_box(0);
v___y_2389_ = v___y_2402_;
v___y_2390_ = v___y_2401_;
v___y_2391_ = v___x_2403_;
goto v___jp_2388_;
}
else
{
lean_object* v___x_2404_; 
v___x_2404_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2389_ = v___y_2402_;
v___y_2390_ = v___y_2401_;
v___y_2391_ = v___x_2404_;
goto v___jp_2388_;
}
}
v___jp_2405_:
{
if (lean_obj_tag(v_name_2381_) == 0)
{
lean_object* v___x_2407_; 
v___x_2407_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2401_ = v___y_2406_;
v___y_2402_ = v___x_2407_;
goto v___jp_2400_;
}
else
{
lean_object* v_val_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_val_2408_ = lean_ctor_get(v_name_2381_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v_name_2381_, 1);
v___x_2409_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2410_ = l_Lean_mkAtom(v_val_2408_);
v___x_2411_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2412_ = lean_array_push(v___x_2411_, v___x_2410_);
v___x_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2386_);
lean_ctor_set(v___x_2413_, 1, v___x_2409_);
lean_ctor_set(v___x_2413_, 2, v___x_2412_);
v___y_2401_ = v___y_2406_;
v___y_2402_ = v___x_2413_;
goto v___jp_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2425_, lean_object* v_term_2426_, lean_object* v_nesting_2427_, lean_object* v_name_2428_, lean_object* v_isPseudoKind_2429_){
_start:
{
uint8_t v_isPseudoKind_boxed_2430_; lean_object* v_res_2431_; 
v_isPseudoKind_boxed_2430_ = lean_unbox(v_isPseudoKind_2429_);
v_res_2431_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2425_, v_term_2426_, v_nesting_2427_, v_name_2428_, v_isPseudoKind_boxed_2430_);
return v_res_2431_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = l_Lean_Syntax_getArg(v_stx_2432_, v___x_2433_);
v___x_2435_ = l_Lean_Syntax_getArgs(v___x_2434_);
lean_dec(v___x_2434_);
v___x_2436_ = lean_array_get_size(v___x_2435_);
lean_dec_ref(v___x_2435_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_nat_dec_eq(v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
uint8_t v___x_2439_; 
v___x_2439_ = 1;
return v___x_2439_;
}
else
{
uint8_t v___x_2440_; 
v___x_2440_ = 0;
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2441_){
_start:
{
uint8_t v_res_2442_; lean_object* v_r_2443_; 
v_res_2442_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2441_);
lean_dec(v_stx_2441_);
v_r_2443_ = lean_box(v_res_2442_);
return v_r_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2444_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = l_Lean_Syntax_isAntiquot(v_stx_2444_);
if (v___x_2445_ == 0)
{
return v_stx_2444_;
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = l_Lean_Syntax_getArg(v_stx_2444_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_getArgs(v___x_2447_);
lean_dec(v___x_2447_);
v___x_2449_ = lean_array_pop(v___x_2448_);
v___x_2450_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2451_ = lean_box(2);
v___x_2452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___x_2450_);
lean_ctor_set(v___x_2452_, 2, v___x_2449_);
v___x_2453_ = l_Lean_Syntax_setArg(v_stx_2444_, v___x_2446_, v___x_2452_);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2454_){
_start:
{
lean_object* v___y_2456_; uint8_t v___x_2467_; 
v___x_2467_ = l_Lean_Syntax_isAntiquot(v_stx_2454_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = lean_unsigned_to_nat(3u);
v___x_2469_ = l_Lean_Syntax_getArg(v_stx_2454_, v___x_2468_);
v___y_2456_ = v___x_2469_;
goto v___jp_2455_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_unsigned_to_nat(2u);
v___x_2471_ = l_Lean_Syntax_getArg(v_stx_2454_, v___x_2470_);
v___y_2456_ = v___x_2471_;
goto v___jp_2455_;
}
v___jp_2455_:
{
uint8_t v___x_2457_; 
v___x_2457_ = l_Lean_Syntax_isIdent(v___y_2456_);
if (v___x_2457_ == 0)
{
uint8_t v___x_2458_; 
v___x_2458_ = l_Lean_Syntax_isAtom(v___y_2456_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = l_Lean_Syntax_getArg(v___y_2456_, v___x_2459_);
lean_dec(v___y_2456_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2461_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2462_ = lean_unsigned_to_nat(1u);
v___x_2463_ = lean_mk_empty_array_with_capacity(v___x_2462_);
v___x_2464_ = lean_array_push(v___x_2463_, v___y_2456_);
v___x_2465_ = lean_box(2);
v___x_2466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2461_);
lean_ctor_set(v___x_2466_, 2, v___x_2464_);
return v___x_2466_;
}
}
else
{
return v___y_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2472_);
lean_dec(v_stx_2472_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2474_){
_start:
{
if (lean_obj_tag(v_x_2474_) == 1)
{
lean_object* v_kind_2475_; 
v_kind_2475_ = lean_ctor_get(v_x_2474_, 1);
if (lean_obj_tag(v_kind_2475_) == 1)
{
lean_object* v_pre_2476_; lean_object* v_str_2477_; 
v_pre_2476_ = lean_ctor_get(v_kind_2475_, 0);
v_str_2477_ = lean_ctor_get(v_kind_2475_, 1);
if (lean_obj_tag(v_pre_2476_) == 1)
{
lean_object* v_pre_2483_; lean_object* v_str_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_pre_2483_ = lean_ctor_get(v_pre_2476_, 0);
v_str_2484_ = lean_ctor_get(v_pre_2476_, 1);
v___x_2485_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2486_ = lean_string_dec_eq(v_str_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2488_ = lean_string_dec_eq(v_str_2477_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_box(0);
return v___x_2489_;
}
else
{
goto v___jp_2478_;
}
}
else
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2491_ = lean_string_dec_eq(v_str_2477_, v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_box(0);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_box(v___x_2491_);
lean_inc(v_pre_2483_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v_pre_2483_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
return v___x_2495_;
}
}
}
else
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2497_ = lean_string_dec_eq(v_str_2477_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_box(0);
return v___x_2498_;
}
else
{
goto v___jp_2478_;
}
}
v___jp_2478_:
{
uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2479_ = 0;
v___x_2480_ = lean_box(v___x_2479_);
lean_inc(v_pre_2476_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_pre_2476_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_box(0);
return v___x_2499_;
}
}
else
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_box(0);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2501_);
lean_dec(v_x_2501_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2503_, size_t v_i_2504_, size_t v_stop_2505_, lean_object* v_b_2506_){
_start:
{
lean_object* v___y_2508_; uint8_t v___x_2512_; 
v___x_2512_ = lean_usize_dec_eq(v_i_2504_, v_stop_2505_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_array_uget_borrowed(v_as_2503_, v_i_2504_);
v___x_2514_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
v___y_2508_ = v_b_2506_;
goto v___jp_2507_;
}
else
{
lean_object* v_val_2515_; lean_object* v___x_2516_; 
v_val_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_val_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = lean_array_push(v_b_2506_, v_val_2515_);
v___y_2508_ = v___x_2516_;
goto v___jp_2507_;
}
}
else
{
return v_b_2506_;
}
v___jp_2507_:
{
size_t v___x_2509_; size_t v___x_2510_; 
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2504_, v___x_2509_);
v_i_2504_ = v___x_2510_;
v_b_2506_ = v___y_2508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2517_, lean_object* v_i_2518_, lean_object* v_stop_2519_, lean_object* v_b_2520_){
_start:
{
size_t v_i_boxed_2521_; size_t v_stop_boxed_2522_; lean_object* v_res_2523_; 
v_i_boxed_2521_ = lean_unbox_usize(v_i_2518_);
lean_dec(v_i_2518_);
v_stop_boxed_2522_ = lean_unbox_usize(v_stop_2519_);
lean_dec(v_stop_2519_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2517_, v_i_boxed_2521_, v_stop_boxed_2522_, v_b_2520_);
lean_dec_ref(v_as_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2526_, lean_object* v_start_2527_, lean_object* v_stop_2528_){
_start:
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2530_ = lean_nat_dec_lt(v_start_2527_, v_stop_2528_);
if (v___x_2530_ == 0)
{
return v___x_2529_;
}
else
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = lean_array_get_size(v_as_2526_);
v___x_2532_ = lean_nat_dec_le(v_stop_2528_, v___x_2531_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_nat_dec_lt(v_start_2527_, v___x_2531_);
if (v___x_2533_ == 0)
{
return v___x_2529_;
}
else
{
size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_usize_of_nat(v_start_2527_);
v___x_2535_ = lean_usize_of_nat(v___x_2531_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2526_, v___x_2534_, v___x_2535_, v___x_2529_);
return v___x_2536_;
}
}
else
{
size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = lean_usize_of_nat(v_start_2527_);
v___x_2538_ = lean_usize_of_nat(v_stop_2528_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2526_, v___x_2537_, v___x_2538_, v___x_2529_);
return v___x_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2540_, lean_object* v_start_2541_, lean_object* v_stop_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2540_, v_start_2541_, v_stop_2542_);
lean_dec(v_stop_2542_);
lean_dec(v_start_2541_);
lean_dec_ref(v_as_2540_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2544_){
_start:
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2544_);
v___x_2546_ = l_Lean_Syntax_isOfKind(v_stx_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2544_);
lean_dec(v_stx_2544_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_box(0);
return v___x_2548_;
}
else
{
lean_object* v_val_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_val_2549_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_val_2549_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_val_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
return v___x_2551_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2552_ = l_Lean_Syntax_getArgs(v_stx_2544_);
lean_dec(v_stx_2544_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = lean_array_get_size(v___x_2552_);
v___x_2555_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2552_, v___x_2553_, v___x_2554_);
lean_dec_ref(v___x_2552_);
v___x_2556_ = lean_array_to_list(v___x_2555_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 1)
{
lean_object* v_kind_2559_; 
v_kind_2559_ = lean_ctor_get(v_x_2558_, 1);
if (lean_obj_tag(v_kind_2559_) == 1)
{
lean_object* v_pre_2560_; lean_object* v_str_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v_pre_2560_ = lean_ctor_get(v_kind_2559_, 0);
v_str_2561_ = lean_ctor_get(v_kind_2559_, 1);
v___x_2562_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2563_ = lean_string_dec_eq(v_str_2561_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_box(0);
return v___x_2564_;
}
else
{
lean_object* v___x_2565_; 
lean_inc(v_pre_2560_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_pre_2560_);
return v___x_2565_;
}
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_box(0);
return v___x_2566_;
}
}
else
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_box(0);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2568_);
lean_dec(v_x_2568_);
return v_res_2569_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
uint8_t v___x_2572_; 
v___x_2572_ = 0;
return v___x_2572_;
}
else
{
uint8_t v___x_2573_; 
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = 1;
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2574_){
_start:
{
uint8_t v_res_2575_; lean_object* v_r_2576_; 
v_res_2575_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2574_);
lean_dec(v_stx_2574_);
v_r_2576_ = lean_box(v_res_2575_);
return v_r_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_unsigned_to_nat(3u);
v___x_2579_ = l_Lean_Syntax_getArg(v_stx_2577_, v___x_2578_);
v___x_2580_ = l_Lean_Syntax_getArgs(v___x_2579_);
lean_dec(v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2581_);
lean_dec(v_stx_2581_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2583_){
_start:
{
uint8_t v___x_2584_; 
v___x_2584_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_unsigned_to_nat(1u);
v___x_2586_ = l_Lean_Syntax_getArg(v_stx_2583_, v___x_2585_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_unsigned_to_nat(5u);
v___x_2588_ = l_Lean_Syntax_getArg(v_stx_2583_, v___x_2587_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2589_);
lean_dec(v_stx_2589_);
return v_res_2590_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2596_ = l_Lean_mkAtom(v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2599_ = l_Lean_mkAtom(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2600_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2601_ = lean_unsigned_to_nat(6u);
v___x_2602_ = lean_mk_empty_array_with_capacity(v___x_2601_);
v___x_2603_ = lean_array_push(v___x_2602_, v___x_2600_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2604_, lean_object* v_contents_2605_, lean_object* v_suffix_2606_, lean_object* v_nesting_2607_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_nesting_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2608_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2609_ = lean_mk_array(v_nesting_2607_, v___x_2608_);
v___x_2610_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2611_ = lean_box(2);
v_nesting_2612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2612_, 0, v___x_2611_);
lean_ctor_set(v_nesting_2612_, 1, v___x_2610_);
lean_ctor_set(v_nesting_2612_, 2, v___x_2609_);
v___x_2613_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2614_ = l_Lean_Name_append(v_kind_2604_, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2611_);
lean_ctor_set(v___x_2616_, 1, v___x_2610_);
lean_ctor_set(v___x_2616_, 2, v_contents_2605_);
v___x_2617_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2618_ = l_Lean_mkAtom(v_suffix_2606_);
v___x_2619_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2620_ = lean_array_push(v___x_2619_, v_nesting_2612_);
v___x_2621_ = lean_array_push(v___x_2620_, v___x_2615_);
v___x_2622_ = lean_array_push(v___x_2621_, v___x_2616_);
v___x_2623_ = lean_array_push(v___x_2622_, v___x_2617_);
v___x_2624_ = lean_array_push(v___x_2623_, v___x_2618_);
v___x_2625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2611_);
lean_ctor_set(v___x_2625_, 1, v___x_2614_);
lean_ctor_set(v___x_2625_, 2, v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2627_){
_start:
{
if (lean_obj_tag(v_x_2627_) == 1)
{
lean_object* v_kind_2628_; 
v_kind_2628_ = lean_ctor_get(v_x_2627_, 1);
if (lean_obj_tag(v_kind_2628_) == 1)
{
lean_object* v_pre_2629_; lean_object* v_str_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_pre_2629_ = lean_ctor_get(v_kind_2628_, 0);
v_str_2630_ = lean_ctor_get(v_kind_2628_, 1);
v___x_2631_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2632_ = lean_string_dec_eq(v_str_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_box(0);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; 
lean_inc(v_pre_2629_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_pre_2629_);
return v___x_2634_;
}
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_box(0);
return v___x_2635_;
}
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_box(0);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2637_);
lean_dec(v_x_2637_);
return v_res_2638_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
uint8_t v___x_2641_; 
v___x_2641_ = 0;
return v___x_2641_;
}
else
{
uint8_t v___x_2642_; 
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = 1;
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2643_){
_start:
{
uint8_t v_res_2644_; lean_object* v_r_2645_; 
v_res_2644_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2643_);
lean_dec(v_stx_2643_);
v_r_2645_ = lean_box(v_res_2644_);
return v_r_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2646_){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = l_Lean_Syntax_getArg(v_stx_2646_, v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2649_);
lean_dec(v_stx_2649_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2653_, lean_object* v_inner_2654_, lean_object* v_suffix_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2656_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2657_ = l_Lean_Name_append(v_kind_2653_, v___x_2656_);
v___x_2658_ = l_Lean_mkAtom(v_suffix_2655_);
v___x_2659_ = lean_unsigned_to_nat(2u);
v___x_2660_ = lean_mk_empty_array_with_capacity(v___x_2659_);
v___x_2661_ = lean_array_push(v___x_2660_, v_inner_2654_);
v___x_2662_ = lean_array_push(v___x_2661_, v___x_2658_);
v___x_2663_ = lean_box(2);
v___x_2664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v___x_2657_);
lean_ctor_set(v___x_2664_, 2, v___x_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2668_){
_start:
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2670_ = l_Lean_Syntax_isOfKind(v_stx_2668_, v___x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2671_){
_start:
{
uint8_t v_res_2672_; lean_object* v_r_2673_; 
v_res_2672_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2671_);
v_r_2673_ = lean_box(v_res_2672_);
return v_r_2673_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2674_){
_start:
{
uint8_t v___y_2676_; uint8_t v___x_2679_; 
v___x_2679_ = l_Lean_Syntax_isAntiquot(v_stx_2674_);
if (v___x_2679_ == 0)
{
uint8_t v___x_2680_; 
v___x_2680_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2674_);
v___y_2676_ = v___x_2680_;
goto v___jp_2675_;
}
else
{
v___y_2676_ = v___x_2679_;
goto v___jp_2675_;
}
v___jp_2675_:
{
if (v___y_2676_ == 0)
{
uint8_t v___x_2677_; 
v___x_2677_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2674_);
if (v___x_2677_ == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2674_);
return v___x_2678_;
}
else
{
lean_dec(v_stx_2674_);
return v___x_2677_;
}
}
else
{
lean_dec(v_stx_2674_);
return v___y_2676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2681_){
_start:
{
uint8_t v_res_2682_; lean_object* v_r_2683_; 
v_res_2682_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2681_);
v_r_2683_ = lean_box(v_res_2682_);
return v_r_2683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2687_, lean_object* v_stx_2688_, lean_object* v_visit_2689_, lean_object* v_stack_2690_, lean_object* v_accept_2691_, lean_object* v_a_2692_, lean_object* v_b_2693_){
_start:
{
lean_object* v_a_2695_; uint8_t v___x_2699_; 
v___x_2699_ = lean_nat_dec_lt(v_a_2692_, v_upperBound_2687_);
if (v___x_2699_ == 0)
{
lean_dec(v_a_2692_);
lean_dec_ref(v_accept_2691_);
lean_dec(v_stack_2690_);
lean_dec_ref(v_visit_2689_);
lean_dec(v_stx_2688_);
lean_inc_ref(v_b_2693_);
return v_b_2693_;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2700_ = lean_box(0);
v___x_2701_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2702_ = l_Lean_Syntax_getArg(v_stx_2688_, v_a_2692_);
lean_inc_ref(v_visit_2689_);
lean_inc(v___x_2702_);
v___x_2703_ = lean_apply_1(v_visit_2689_, v___x_2702_);
v___x_2704_ = lean_unbox(v___x_2703_);
if (v___x_2704_ == 0)
{
lean_dec(v___x_2702_);
v_a_2695_ = v___x_2701_;
goto v___jp_2694_;
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_inc(v_a_2692_);
lean_inc(v_stx_2688_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_stx_2688_);
lean_ctor_set(v___x_2705_, 1, v_a_2692_);
lean_inc(v_stack_2690_);
v___x_2706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
lean_ctor_set(v___x_2706_, 1, v_stack_2690_);
lean_inc_ref(v_accept_2691_);
lean_inc_ref(v_visit_2689_);
v___x_2707_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2689_, v_accept_2691_, v___x_2706_, v___x_2702_);
if (lean_obj_tag(v___x_2707_) == 1)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_a_2692_);
lean_dec_ref(v_accept_2691_);
lean_dec(v_stack_2690_);
lean_dec_ref(v_visit_2689_);
lean_dec(v_stx_2688_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2700_);
return v___x_2709_;
}
else
{
lean_dec(v___x_2707_);
v_a_2695_ = v___x_2701_;
goto v___jp_2694_;
}
}
}
v___jp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_a_2692_, v___x_2696_);
lean_dec(v_a_2692_);
v_a_2692_ = v___x_2697_;
v_b_2693_ = v_a_2695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2710_, lean_object* v_accept_2711_, lean_object* v_stack_2712_, lean_object* v_stx_2713_){
_start:
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
lean_inc_ref(v_accept_2711_);
lean_inc(v_stx_2713_);
v___x_2714_ = lean_apply_1(v_accept_2711_, v_stx_2713_);
v___x_2715_ = lean_unbox(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v_fst_2721_; 
v___x_2716_ = l_Lean_Syntax_getNumArgs(v_stx_2713_);
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = lean_box(0);
v___x_2719_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2716_, v_stx_2713_, v_visit_2710_, v_stack_2712_, v_accept_2711_, v___x_2717_, v___x_2719_);
lean_dec(v___x_2716_);
v_fst_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_fst_2721_);
lean_dec_ref(v___x_2720_);
if (lean_obj_tag(v_fst_2721_) == 0)
{
return v___x_2718_;
}
else
{
lean_object* v_val_2722_; 
v_val_2722_ = lean_ctor_get(v_fst_2721_, 0);
lean_inc(v_val_2722_);
lean_dec_ref_known(v_fst_2721_, 1);
return v_val_2722_;
}
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v_accept_2711_);
lean_dec_ref(v_visit_2710_);
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_stx_2713_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_stack_2712_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2727_, lean_object* v_stx_2728_, lean_object* v_visit_2729_, lean_object* v_stack_2730_, lean_object* v_accept_2731_, lean_object* v_a_2732_, lean_object* v_b_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2727_, v_stx_2728_, v_visit_2729_, v_stack_2730_, v_accept_2731_, v_a_2732_, v_b_2733_);
lean_dec_ref(v_b_2733_);
lean_dec(v_upperBound_2727_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2735_, lean_object* v_stx_2736_, lean_object* v_visit_2737_, lean_object* v_stack_2738_, lean_object* v_accept_2739_, lean_object* v_inst_2740_, lean_object* v_R_2741_, lean_object* v_a_2742_, lean_object* v_b_2743_, lean_object* v_c_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2735_, v_stx_2736_, v_visit_2737_, v_stack_2738_, v_accept_2739_, v_a_2742_, v_b_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2746_, lean_object* v_stx_2747_, lean_object* v_visit_2748_, lean_object* v_stack_2749_, lean_object* v_accept_2750_, lean_object* v_inst_2751_, lean_object* v_R_2752_, lean_object* v_a_2753_, lean_object* v_b_2754_, lean_object* v_c_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2746_, v_stx_2747_, v_visit_2748_, v_stack_2749_, v_accept_2750_, v_inst_2751_, v_R_2752_, v_a_2753_, v_b_2754_, v_c_2755_);
lean_dec_ref(v_b_2754_);
lean_dec(v_upperBound_2746_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2757_, lean_object* v_visit_2758_, lean_object* v_accept_2759_){
_start:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
lean_inc_ref(v_visit_2758_);
lean_inc(v_root_2757_);
v___x_2760_ = lean_apply_1(v_visit_2758_, v_root_2757_);
v___x_2761_ = lean_unbox(v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_dec_ref(v_accept_2759_);
lean_dec_ref(v_visit_2758_);
lean_dec(v_root_2757_);
v___x_2762_ = lean_box(0);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_box(0);
v___x_2764_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2758_, v_accept_2759_, v___x_2763_, v_root_2757_);
return v___x_2764_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2765_, lean_object* v_x_2766_, lean_object* v_p_2767_){
_start:
{
if (lean_obj_tag(v_p_2767_) == 0)
{
lean_dec_ref(v_x_2766_);
return v___x_2765_;
}
else
{
lean_object* v_fst_2768_; lean_object* v_val_2769_; uint8_t v___x_2770_; 
v_fst_2768_ = lean_ctor_get(v_x_2766_, 0);
lean_inc(v_fst_2768_);
lean_dec_ref(v_x_2766_);
v_val_2769_ = lean_ctor_get(v_p_2767_, 0);
v___x_2770_ = l_Lean_Syntax_isOfKind(v_fst_2768_, v_val_2769_);
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2771_, lean_object* v_x_2772_, lean_object* v_p_2773_){
_start:
{
uint8_t v___x_123__boxed_2774_; uint8_t v_res_2775_; lean_object* v_r_2776_; 
v___x_123__boxed_2774_ = lean_unbox(v___x_2771_);
v_res_2775_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2774_, v_x_2772_, v_p_2773_);
lean_dec(v_p_2773_);
v_r_2776_ = lean_box(v_res_2775_);
return v_r_2776_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2777_){
_start:
{
if (lean_obj_tag(v_x_2777_) == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = 1;
return v___x_2778_;
}
else
{
lean_object* v_head_2779_; uint8_t v___x_2780_; 
v_head_2779_ = lean_ctor_get(v_x_2777_, 0);
v___x_2780_ = lean_unbox(v_head_2779_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_unbox(v_head_2779_);
return v___x_2781_;
}
else
{
lean_object* v_tail_2782_; 
v_tail_2782_ = lean_ctor_get(v_x_2777_, 1);
v_x_2777_ = v_tail_2782_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2784_){
_start:
{
uint8_t v_res_2785_; lean_object* v_r_2786_; 
v_res_2785_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2784_);
lean_dec(v_x_2784_);
v_r_2786_ = lean_box(v_res_2785_);
return v_r_2786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2789_, lean_object* v_pattern_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2791_ = l_List_lengthTR___redArg(v_pattern_2790_);
v___x_2792_ = l_List_lengthTR___redArg(v_stack_2789_);
v___x_2793_ = lean_nat_dec_le(v___x_2791_, v___x_2792_);
lean_dec(v___x_2792_);
lean_dec(v___x_2791_);
if (v___x_2793_ == 0)
{
lean_dec(v_pattern_2790_);
lean_dec(v_stack_2789_);
return v___x_2793_;
}
else
{
lean_object* v___x_2794_; lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2794_ = lean_box(v___x_2793_);
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2795_, 0, v___x_2794_);
v___x_2796_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2797_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2795_, v_stack_2789_, v_pattern_2790_, v___x_2796_);
v___x_2798_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2797_);
lean_dec(v___x_2797_);
return v___x_2798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2799_, lean_object* v_pattern_2800_){
_start:
{
uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_res_2801_ = l_Lean_Syntax_Stack_matches(v_stack_2799_, v_pattern_2800_);
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2803_, lean_object* v_trailing_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2803_);
if (lean_obj_tag(v___x_2805_) == 1)
{
lean_object* v_val_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2841_; 
v_val_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2841_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_val_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2841_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
if (lean_obj_tag(v_val_2806_) == 0)
{
lean_object* v_trailing_2810_; lean_object* v_leading_2811_; lean_object* v_pos_2812_; lean_object* v_endPos_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2839_; 
v_trailing_2810_ = lean_ctor_get(v_val_2806_, 2);
v_leading_2811_ = lean_ctor_get(v_val_2806_, 0);
v_pos_2812_ = lean_ctor_get(v_val_2806_, 1);
v_endPos_2813_ = lean_ctor_get(v_val_2806_, 3);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_val_2806_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2815_ = v_val_2806_;
v_isShared_2816_ = v_isSharedCheck_2839_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_endPos_2813_);
lean_inc(v_trailing_2810_);
lean_inc(v_pos_2812_);
lean_inc(v_leading_2811_);
lean_dec(v_val_2806_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2839_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_str_2817_; lean_object* v_startPos_2818_; lean_object* v_stopPos_2819_; lean_object* v_startPos_2820_; lean_object* v_stopPos_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2837_; 
v_str_2817_ = lean_ctor_get(v_trailing_2810_, 0);
lean_inc_ref(v_str_2817_);
v_startPos_2818_ = lean_ctor_get(v_trailing_2810_, 1);
lean_inc(v_startPos_2818_);
v_stopPos_2819_ = lean_ctor_get(v_trailing_2810_, 2);
lean_inc(v_stopPos_2819_);
lean_dec_ref(v_trailing_2810_);
v_startPos_2820_ = lean_ctor_get(v_trailing_2804_, 1);
v_stopPos_2821_ = lean_ctor_get(v_trailing_2804_, 2);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_trailing_2804_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v_trailing_2804_, 0);
lean_dec(v_unused_2838_);
v___x_2823_ = v_trailing_2804_;
v_isShared_2824_ = v_isSharedCheck_2837_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_stopPos_2821_);
lean_inc(v_startPos_2820_);
lean_dec(v_trailing_2804_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2837_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint8_t v_decide_2825_; 
v_decide_2825_ = lean_nat_dec_eq(v_stopPos_2819_, v_startPos_2820_);
lean_dec(v_startPos_2820_);
lean_dec(v_stopPos_2819_);
if (v_decide_2825_ == 0)
{
lean_object* v___x_2826_; 
lean_del_object(v___x_2823_);
lean_dec(v_stopPos_2821_);
lean_dec(v_startPos_2818_);
lean_dec_ref(v_str_2817_);
lean_del_object(v___x_2815_);
lean_dec(v_endPos_2813_);
lean_dec(v_pos_2812_);
lean_dec_ref(v_leading_2811_);
lean_del_object(v___x_2808_);
lean_dec(v_stx_2803_);
v___x_2826_ = lean_box(0);
return v___x_2826_;
}
else
{
lean_object* v_trailing_2828_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_startPos_2818_);
lean_ctor_set(v___x_2823_, 0, v_str_2817_);
v_trailing_2828_ = v___x_2823_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_str_2817_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_startPos_2818_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_stopPos_2821_);
v_trailing_2828_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 2, v_trailing_2828_);
v___x_2830_ = v___x_2815_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_leading_2811_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_pos_2812_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_trailing_2828_);
lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_endPos_2813_);
v___x_2830_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2831_ = l_Lean_Syntax_setTailInfo(v_stx_2803_, v___x_2830_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2831_);
v___x_2833_ = v___x_2808_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2840_; 
lean_del_object(v___x_2808_);
lean_dec(v_val_2806_);
lean_dec_ref(v_trailing_2804_);
lean_dec(v_stx_2803_);
v___x_2840_ = lean_box(0);
return v___x_2840_;
}
}
}
else
{
lean_object* v___x_2842_; 
lean_dec(v___x_2805_);
lean_dec_ref(v_trailing_2804_);
lean_dec(v_stx_2803_);
v___x_2842_ = lean_box(0);
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2843_, lean_object* v_trailing_2844_){
_start:
{
lean_object* v___x_2845_; 
lean_inc(v_stx_2843_);
v___x_2845_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2843_, v_trailing_2844_);
if (lean_obj_tag(v___x_2845_) == 0)
{
return v_stx_2843_;
}
else
{
lean_object* v_val_2846_; 
lean_dec(v_stx_2843_);
v_val_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v___x_2845_, 1);
return v_val_2846_;
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

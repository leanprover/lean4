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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v_leading_924_; lean_object* v_trailing_925_; lean_object* v_pos_926_; lean_object* v_endPos_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_954_; 
v_leading_924_ = lean_ctor_get(v_x_921_, 0);
v_trailing_925_ = lean_ctor_get(v_x_921_, 2);
v_pos_926_ = lean_ctor_get(v_x_921_, 1);
v_endPos_927_ = lean_ctor_get(v_x_921_, 3);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_921_);
if (v_isSharedCheck_954_ == 0)
{
v___x_929_ = v_x_921_;
v_isShared_930_ = v_isSharedCheck_954_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_endPos_927_);
lean_inc(v_trailing_925_);
lean_inc(v_pos_926_);
lean_inc(v_leading_924_);
lean_dec(v_x_921_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_954_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_str_931_; lean_object* v_stopPos_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_952_; 
v_str_931_ = lean_ctor_get(v_leading_924_, 0);
v_stopPos_932_ = lean_ctor_get(v_leading_924_, 2);
v_isSharedCheck_952_ = !lean_is_exclusive(v_leading_924_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v_leading_924_, 1);
lean_dec(v_unused_953_);
v___x_934_ = v_leading_924_;
v_isShared_935_ = v_isSharedCheck_952_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_stopPos_932_);
lean_inc(v_str_931_);
lean_dec(v_leading_924_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_952_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_str_936_; lean_object* v_startPos_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_950_; 
v_str_936_ = lean_ctor_get(v_trailing_925_, 0);
v_startPos_937_ = lean_ctor_get(v_trailing_925_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_trailing_925_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_trailing_925_, 2);
lean_dec(v_unused_951_);
v___x_939_ = v_trailing_925_;
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_startPos_937_);
lean_inc(v_str_936_);
lean_dec(v_trailing_925_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 2, v_stopPos_932_);
lean_ctor_set(v___x_939_, 1, v_x_922_);
lean_ctor_set(v___x_939_, 0, v_str_931_);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_str_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_x_922_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_stopPos_932_);
v___x_942_ = v_reuseFailAlloc_949_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 2, v_x_923_);
lean_ctor_set(v___x_934_, 1, v_startPos_937_);
lean_ctor_set(v___x_934_, 0, v_str_936_);
v___x_944_ = v___x_934_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_str_936_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_startPos_937_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_x_923_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 2, v___x_944_);
lean_ctor_set(v___x_929_, 0, v___x_942_);
v___x_946_ = v___x_929_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_pos_926_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_endPos_927_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_923_);
lean_dec(v_x_922_);
return v_x_921_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_955_, lean_object* v___x_956_, lean_object* v___x_957_, lean_object* v_a_958_, lean_object* v_b_959_){
_start:
{
lean_object* v___x_960_; uint8_t v_decide_961_; 
v___x_960_ = lean_nat_sub(v___x_955_, v___x_956_);
v_decide_961_ = lean_nat_dec_eq(v_a_958_, v___x_960_);
lean_dec(v___x_960_);
if (v_decide_961_ == 0)
{
uint32_t v___x_962_; lean_object* v___x_963_; uint32_t v___x_964_; uint8_t v___x_965_; 
v___x_962_ = 10;
v___x_963_ = lean_nat_add(v___x_956_, v_a_958_);
v___x_964_ = lean_string_utf8_get_fast(v___x_957_, v___x_963_);
v___x_965_ = lean_uint32_dec_eq(v___x_964_, v___x_962_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_a_958_);
v___x_966_ = lean_box(0);
v___x_967_ = lean_string_utf8_next_fast(v___x_957_, v___x_963_);
lean_dec(v___x_963_);
v___x_968_ = lean_nat_sub(v___x_967_, v___x_956_);
v_a_958_ = v___x_968_;
v_b_959_ = v___x_966_;
goto _start;
}
else
{
lean_object* v___x_970_; 
lean_dec(v___x_963_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_a_958_);
return v___x_970_;
}
}
else
{
lean_dec(v_a_958_);
lean_inc(v_b_959_);
return v_b_959_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_971_, v___x_972_, v___x_973_, v_a_974_, v_b_975_);
lean_dec(v_b_975_);
lean_dec_ref(v___x_973_);
lean_dec(v___x_972_);
lean_dec(v___x_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_977_){
_start:
{
lean_object* v_str_978_; lean_object* v_startPos_979_; lean_object* v_stopPos_980_; uint8_t v___x_984_; 
v_str_978_ = lean_ctor_get(v_trail_977_, 0);
v_startPos_979_ = lean_ctor_get(v_trail_977_, 1);
v_stopPos_980_ = lean_ctor_get(v_trail_977_, 2);
v___x_984_ = lean_string_is_valid_pos(v_str_978_, v_startPos_979_);
if (v___x_984_ == 0)
{
goto v___jp_981_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = lean_string_is_valid_pos(v_str_978_, v_stopPos_980_);
if (v___x_985_ == 0)
{
goto v___jp_981_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = lean_nat_dec_le(v_startPos_979_, v_stopPos_980_);
if (v___x_986_ == 0)
{
goto v___jp_981_;
}
else
{
lean_object* v_searcher_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_searcher_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_box(0);
v___x_989_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v_stopPos_980_, v_startPos_979_, v_str_978_, v_searcher_987_, v___x_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_nat_sub(v_stopPos_980_, v_startPos_979_);
v___x_991_ = lean_nat_add(v_startPos_979_, v___x_990_);
lean_dec(v___x_990_);
return v___x_991_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_993_; 
v_val_992_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_989_, 1);
v___x_993_ = lean_nat_add(v_startPos_979_, v_val_992_);
lean_dec(v_val_992_);
return v___x_993_;
}
}
}
}
v___jp_981_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_nat_sub(v_stopPos_980_, v_startPos_979_);
v___x_983_ = lean_nat_add(v_startPos_979_, v___x_982_);
lean_dec(v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object* v_trail_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trail_994_);
lean_dec_ref(v_trail_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v___x_998_, lean_object* v___x_999_, lean_object* v_inst_1000_, lean_object* v_R_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_, lean_object* v_c_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_996_, v___x_997_, v___x_999_, v_a_1002_, v_b_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v_inst_1010_, lean_object* v_R_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_, lean_object* v_c_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1006_, v___x_1007_, v___x_1008_, v___x_1009_, v_inst_1010_, v_R_1011_, v_a_1012_, v_b_1013_, v_c_1014_);
lean_dec(v_b_1013_);
lean_dec_ref(v___x_1009_);
lean_dec_ref(v___x_1008_);
lean_dec(v___x_1007_);
lean_dec(v___x_1006_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___y_1019_; 
switch(lean_obj_tag(v_x_1016_))
{
case 2:
{
lean_object* v_info_1022_; 
v_info_1022_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_info_1022_);
if (lean_obj_tag(v_info_1022_) == 0)
{
lean_object* v_val_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1035_; 
v_val_1023_ = lean_ctor_get(v_x_1016_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v_x_1016_, 0);
lean_dec(v_unused_1036_);
v___x_1025_ = v_x_1016_;
v_isShared_1026_ = v_isSharedCheck_1035_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_val_1023_);
lean_dec(v_x_1016_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1035_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_trailing_1027_; lean_object* v_trailStop_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v_trailing_1027_ = lean_ctor_get(v_info_1022_, 2);
v_trailStop_1028_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1027_);
lean_inc(v_trailStop_1028_);
v___x_1029_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1022_, v_a_1017_, v_trailStop_1028_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_val_1023_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v_trailStop_1028_);
return v___x_1033_;
}
}
}
else
{
lean_dec_ref_known(v_x_1016_, 2);
lean_dec(v_info_1022_);
v___y_1019_ = v_a_1017_;
goto v___jp_1018_;
}
}
case 3:
{
lean_object* v_info_1037_; 
v_info_1037_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_info_1037_);
if (lean_obj_tag(v_info_1037_) == 0)
{
lean_object* v_rawVal_1038_; lean_object* v_val_1039_; lean_object* v_preresolved_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1052_; 
v_rawVal_1038_ = lean_ctor_get(v_x_1016_, 1);
v_val_1039_ = lean_ctor_get(v_x_1016_, 2);
v_preresolved_1040_ = lean_ctor_get(v_x_1016_, 3);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_x_1016_, 0);
lean_dec(v_unused_1053_);
v___x_1042_ = v_x_1016_;
v_isShared_1043_ = v_isSharedCheck_1052_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_preresolved_1040_);
lean_inc(v_val_1039_);
lean_inc(v_rawVal_1038_);
lean_dec(v_x_1016_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1052_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_trailing_1044_; lean_object* v_trailStop_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v_trailing_1044_ = lean_ctor_get(v_info_1037_, 2);
v_trailStop_1045_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1044_);
lean_inc(v_trailStop_1045_);
v___x_1046_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1037_, v_a_1017_, v_trailStop_1045_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1046_);
v___x_1048_ = v___x_1042_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_rawVal_1038_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_val_1039_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_preresolved_1040_);
v___x_1048_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_trailStop_1045_);
return v___x_1050_;
}
}
}
else
{
lean_dec_ref_known(v_x_1016_, 4);
lean_dec(v_info_1037_);
v___y_1019_ = v_a_1017_;
goto v___jp_1018_;
}
}
default: 
{
lean_dec(v_x_1016_);
v___y_1019_ = v_a_1017_;
goto v___jp_1018_;
}
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___y_1019_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
switch(lean_obj_tag(v___y_1054_))
{
case 2:
{
lean_object* v_info_1059_; 
v_info_1059_ = lean_ctor_get(v___y_1054_, 0);
lean_inc(v_info_1059_);
if (lean_obj_tag(v_info_1059_) == 0)
{
lean_object* v_val_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1072_; 
v_val_1060_ = lean_ctor_get(v___y_1054_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___y_1054_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___y_1054_, 0);
lean_dec(v_unused_1073_);
v___x_1062_ = v___y_1054_;
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_val_1060_);
lean_dec(v___y_1054_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v_trailing_1064_; lean_object* v_trailStop_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v_trailing_1064_ = lean_ctor_get(v_info_1059_, 2);
v_trailStop_1065_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1064_);
lean_inc(v_trailStop_1065_);
v___x_1066_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1059_, v___y_1055_, v_trailStop_1065_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1066_);
v___x_1068_ = v___x_1062_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_val_1060_);
v___x_1068_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_trailStop_1065_);
return v___x_1070_;
}
}
}
else
{
lean_dec_ref_known(v___y_1054_, 2);
lean_dec(v_info_1059_);
goto v___jp_1056_;
}
}
case 3:
{
lean_object* v_info_1074_; 
v_info_1074_ = lean_ctor_get(v___y_1054_, 0);
lean_inc(v_info_1074_);
if (lean_obj_tag(v_info_1074_) == 0)
{
lean_object* v_rawVal_1075_; lean_object* v_val_1076_; lean_object* v_preresolved_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1089_; 
v_rawVal_1075_ = lean_ctor_get(v___y_1054_, 1);
v_val_1076_ = lean_ctor_get(v___y_1054_, 2);
v_preresolved_1077_ = lean_ctor_get(v___y_1054_, 3);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___y_1054_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___y_1054_, 0);
lean_dec(v_unused_1090_);
v___x_1079_ = v___y_1054_;
v_isShared_1080_ = v_isSharedCheck_1089_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_preresolved_1077_);
lean_inc(v_val_1076_);
lean_inc(v_rawVal_1075_);
lean_dec(v___y_1054_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1089_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_trailing_1081_; lean_object* v_trailStop_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v_trailing_1081_ = lean_ctor_get(v_info_1074_, 2);
v_trailStop_1082_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1081_);
lean_inc(v_trailStop_1082_);
v___x_1083_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1074_, v___y_1055_, v_trailStop_1082_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1083_);
v___x_1085_ = v___x_1079_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_rawVal_1075_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_val_1076_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_preresolved_1077_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_trailStop_1082_);
return v___x_1087_;
}
}
}
else
{
lean_dec_ref_known(v___y_1054_, 4);
lean_dec(v_info_1074_);
goto v___jp_1056_;
}
}
default: 
{
lean_dec(v___y_1054_);
goto v___jp_1056_;
}
}
v___jp_1056_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___y_1055_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1091_, lean_object* v___y_1092_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 1)
{
lean_object* v_info_1093_; lean_object* v_kind_1094_; lean_object* v_args_1095_; lean_object* v___x_1096_; lean_object* v_fst_1097_; 
v_info_1093_ = lean_ctor_get(v_x_1091_, 0);
lean_inc(v_info_1093_);
v_kind_1094_ = lean_ctor_get(v_x_1091_, 1);
lean_inc(v_kind_1094_);
v_args_1095_ = lean_ctor_get(v_x_1091_, 2);
lean_inc_ref(v_args_1095_);
v___x_1096_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1091_, v___y_1092_);
v_fst_1097_ = lean_ctor_get(v___x_1096_, 0);
if (lean_obj_tag(v_fst_1097_) == 0)
{
lean_object* v_snd_1098_; size_t v_sz_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1111_; 
v_snd_1098_ = lean_ctor_get(v___x_1096_, 1);
lean_inc(v_snd_1098_);
lean_dec_ref(v___x_1096_);
v_sz_1099_ = lean_array_size(v_args_1095_);
v___x_1100_ = ((size_t)0ULL);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1099_, v___x_1100_, v_args_1095_, v_snd_1098_);
v_fst_1102_ = lean_ctor_get(v___x_1101_, 0);
v_snd_1103_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1105_ = v___x_1101_;
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_snd_1103_);
lean_inc(v_fst_1102_);
lean_dec(v___x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1107_, 0, v_info_1093_);
lean_ctor_set(v___x_1107_, 1, v_kind_1094_);
lean_ctor_set(v___x_1107_, 2, v_fst_1102_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1103_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
lean_inc_ref(v_fst_1097_);
lean_dec_ref(v_args_1095_);
lean_dec(v_kind_1094_);
lean_dec(v_info_1093_);
v_snd_1112_ = lean_ctor_get(v___x_1096_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v___x_1096_, 0);
lean_dec(v_unused_1121_);
v___x_1114_ = v___x_1096_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_dec(v___x_1096_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_val_1116_; lean_object* v___x_1118_; 
v_val_1116_ = lean_ctor_get(v_fst_1097_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v_fst_1097_, 1);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_val_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_val_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_snd_1112_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v_fst_1123_; 
lean_inc(v_x_1091_);
v___x_1122_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1091_, v___y_1092_);
v_fst_1123_ = lean_ctor_get(v___x_1122_, 0);
if (lean_obj_tag(v_fst_1123_) == 0)
{
lean_object* v_snd_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
v_snd_1124_ = lean_ctor_get(v___x_1122_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1122_, 0);
lean_dec(v_unused_1132_);
v___x_1126_ = v___x_1122_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snd_1124_);
lean_dec(v___x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_x_1091_);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_x_1091_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_snd_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
lean_inc_ref(v_fst_1123_);
lean_dec(v_x_1091_);
v_snd_1133_ = lean_ctor_get(v___x_1122_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1122_, 0);
lean_dec(v_unused_1142_);
v___x_1135_ = v___x_1122_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_dec(v___x_1122_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_val_1137_; lean_object* v___x_1139_; 
v_val_1137_ = lean_ctor_get(v_fst_1123_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v_fst_1123_, 1);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_val_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_val_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_snd_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_bs_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_bs_1145_);
lean_ctor_set(v___x_1148_, 1, v___y_1146_);
return v___x_1148_;
}
else
{
lean_object* v_v_1149_; lean_object* v___x_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1153_; lean_object* v_bs_x27_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v_v_1149_ = lean_array_uget_borrowed(v_bs_1145_, v_i_1144_);
lean_inc(v_v_1149_);
v___x_1150_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1149_, v___y_1146_);
v_fst_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_fst_1151_);
v_snd_1152_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_snd_1152_);
lean_dec_ref(v___x_1150_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v_bs_x27_1154_ = lean_array_uset(v_bs_1145_, v_i_1144_, v___x_1153_);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1144_, v___x_1155_);
v___x_1157_ = lean_array_uset(v_bs_x27_1154_, v_i_1144_, v_fst_1151_);
v_i_1144_ = v___x_1156_;
v_bs_1145_ = v___x_1157_;
v___y_1146_ = v_snd_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_bs_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1163_, v_i_boxed_1164_, v_bs_1161_, v___y_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_fst_1169_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1166_, v___x_1167_);
v_fst_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_fst_1169_);
lean_dec_ref(v___x_1168_);
return v_fst_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1170_, lean_object* v_x_1171_){
_start:
{
switch(lean_obj_tag(v_x_1171_))
{
case 2:
{
lean_object* v_info_1172_; lean_object* v_val_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
v_info_1172_ = lean_ctor_get(v_x_1171_, 0);
v_val_1173_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v_x_1171_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_val_1173_);
lean_inc(v_info_1172_);
lean_dec(v_x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1170_, v_info_1172_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_val_1173_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
case 3:
{
lean_object* v_info_1182_; lean_object* v_rawVal_1183_; lean_object* v_val_1184_; lean_object* v_preresolved_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1193_; 
v_info_1182_ = lean_ctor_get(v_x_1171_, 0);
v_rawVal_1183_ = lean_ctor_get(v_x_1171_, 1);
v_val_1184_ = lean_ctor_get(v_x_1171_, 2);
v_preresolved_1185_ = lean_ctor_get(v_x_1171_, 3);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1187_ = v_x_1171_;
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_preresolved_1185_);
lean_inc(v_val_1184_);
lean_inc(v_rawVal_1183_);
lean_inc(v_info_1182_);
lean_dec(v_x_1171_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1170_, v_info_1182_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_rawVal_1183_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_val_1184_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_preresolved_1185_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
case 1:
{
lean_object* v_info_1194_; lean_object* v_kind_1195_; lean_object* v_args_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_info_1194_ = lean_ctor_get(v_x_1171_, 0);
v_kind_1195_ = lean_ctor_get(v_x_1171_, 1);
v_args_1196_ = lean_ctor_get(v_x_1171_, 2);
v___x_1197_ = lean_array_get_size(v_args_1196_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_nat_dec_eq(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1211_; 
lean_inc_ref(v_args_1196_);
lean_inc(v_kind_1195_);
lean_inc(v_info_1194_);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; lean_object* v_unused_1213_; lean_object* v_unused_1214_; 
v_unused_1212_ = lean_ctor_get(v_x_1171_, 2);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_x_1171_, 1);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_x_1171_, 0);
lean_dec(v_unused_1214_);
v___x_1201_ = v_x_1171_;
v_isShared_1202_ = v_isSharedCheck_1211_;
goto v_resetjp_1200_;
}
else
{
lean_dec(v_x_1171_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1211_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v_i_1204_; lean_object* v___x_1205_; lean_object* v_last_1206_; lean_object* v_args_1207_; lean_object* v___x_1209_; 
v___x_1203_ = lean_unsigned_to_nat(1u);
v_i_1204_ = lean_nat_sub(v___x_1197_, v___x_1203_);
v___x_1205_ = lean_array_fget_borrowed(v_args_1196_, v_i_1204_);
lean_inc(v___x_1205_);
v_last_1206_ = l_Lean_Syntax_updateTrailing(v_trailing_1170_, v___x_1205_);
v_args_1207_ = lean_array_fset(v_args_1196_, v_i_1204_, v_last_1206_);
lean_dec(v_i_1204_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 2, v_args_1207_);
v___x_1209_ = v___x_1201_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_info_1194_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_kind_1195_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_args_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_dec_ref(v_trailing_1170_);
return v_x_1171_;
}
}
default: 
{
lean_dec_ref(v_trailing_1170_);
return v_x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
return v_x_1215_;
}
else
{
lean_object* v_head_1217_; lean_object* v_tail_1218_; lean_object* v___x_1219_; 
v_head_1217_ = lean_ctor_get(v_x_1216_, 0);
lean_inc(v_head_1217_);
v_tail_1218_ = lean_ctor_get(v_x_1216_, 1);
lean_inc(v_tail_1218_);
lean_dec_ref_known(v_x_1216_, 2);
v___x_1219_ = l_Lean_Name_append(v_x_1215_, v_head_1217_);
v_x_1215_ = v___x_1219_;
v_x_1216_ = v_tail_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1223_, lean_object* v_nFields_x3f_1224_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v_nameComps_1226_; lean_object* v___x_1227_; lean_object* v_nPrefix_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_namePrefix_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_val_1225_ = lean_ctor_get(v_nFields_x3f_1224_, 0);
v_nameComps_1226_ = l_Lean_Name_components(v_n_1223_);
v___x_1227_ = l_List_lengthTR___redArg(v_nameComps_1226_);
v_nPrefix_1228_ = lean_nat_sub(v___x_1227_, v_val_1225_);
lean_dec(v___x_1227_);
v___x_1229_ = lean_box(0);
v___x_1230_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1228_);
lean_inc(v_nameComps_1226_);
v___x_1231_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1226_, v_nameComps_1226_, v_nPrefix_1228_, v___x_1230_);
v_namePrefix_1232_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1229_, v___x_1231_);
v___x_1233_ = l_List_drop___redArg(v_nPrefix_1228_, v_nameComps_1226_);
lean_dec(v_nameComps_1226_);
v___x_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_namePrefix_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Name_components(v_n_1223_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1236_, lean_object* v_nFields_x3f_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1236_, v_nFields_x3f_1237_);
lean_dec(v_nFields_x3f_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_panic_fn_borrowed(v___x_1240_, v_msg_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
return v_x_1242_;
}
else
{
lean_object* v_head_1244_; lean_object* v_tail_1245_; lean_object* v_startPos_1246_; lean_object* v_stopPos_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_head_1244_ = lean_ctor_get(v_x_1243_, 0);
v_tail_1245_ = lean_ctor_get(v_x_1243_, 1);
v_startPos_1246_ = lean_ctor_get(v_head_1244_, 1);
v_stopPos_1247_ = lean_ctor_get(v_head_1244_, 2);
v___x_1248_ = lean_nat_sub(v_stopPos_1247_, v_startPos_1246_);
v___x_1249_ = lean_nat_add(v_x_1242_, v___x_1248_);
lean_dec(v___x_1248_);
lean_dec(v_x_1242_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v___x_1249_, v___x_1250_);
lean_dec(v___x_1249_);
v_x_1242_ = v___x_1251_;
v_x_1243_ = v_tail_1245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1253_, v_x_1254_);
lean_dec(v_x_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1260_, lean_object* v_pos_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = l_List_reverse___redArg(v_a_1263_);
return v___x_1264_;
}
else
{
lean_object* v_head_1265_; lean_object* v_tail_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1284_; 
v_head_1265_ = lean_ctor_get(v_a_1262_, 0);
v_tail_1266_ = lean_ctor_get(v_a_1262_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1268_ = v_a_1262_;
v_isShared_1269_ = v_isSharedCheck_1284_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_tail_1266_);
lean_inc(v_head_1265_);
lean_dec(v_a_1262_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1284_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_stopPos_1270_; lean_object* v_startPos_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_info_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v_stopPos_1270_ = lean_ctor_get(v_head_1265_, 2);
lean_inc(v_stopPos_1270_);
lean_dec(v_head_1265_);
v_startPos_1271_ = lean_ctor_get(v_rawVal_1260_, 1);
v___x_1272_ = lean_nat_sub(v_stopPos_1270_, v_startPos_1271_);
lean_dec(v_stopPos_1270_);
v___x_1273_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1274_ = lean_nat_add(v___x_1272_, v_pos_1261_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v___x_1275_, v___x_1274_);
v_info_1277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1277_, 0, v___x_1273_);
lean_ctor_set(v_info_1277_, 1, v___x_1274_);
lean_ctor_set(v_info_1277_, 2, v___x_1273_);
lean_ctor_set(v_info_1277_, 3, v___x_1276_);
v___x_1278_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_info_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_a_1263_);
lean_ctor_set(v___x_1268_, 0, v___x_1279_);
v___x_1281_ = v___x_1268_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1263_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v_a_1262_ = v_tail_1266_;
v_a_1263_ = v___x_1281_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1285_, lean_object* v_pos_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1285_, v_pos_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_pos_1286_);
lean_dec_ref(v_rawVal_1285_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1290_, lean_object* v_pos_1291_, lean_object* v_trailing_1292_, lean_object* v_leading_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
if (lean_obj_tag(v_a_1294_) == 0)
{
lean_object* v___x_1296_; 
lean_dec_ref(v_leading_1293_);
lean_dec_ref(v_trailing_1292_);
v___x_1296_ = l_List_reverse___redArg(v_a_1295_);
return v___x_1296_;
}
else
{
lean_object* v_head_1297_; lean_object* v_snd_1298_; lean_object* v_tail_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1329_; 
v_head_1297_ = lean_ctor_get(v_a_1294_, 0);
lean_inc(v_head_1297_);
v_snd_1298_ = lean_ctor_get(v_head_1297_, 1);
lean_inc(v_snd_1298_);
v_tail_1299_ = lean_ctor_get(v_a_1294_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_a_1294_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_a_1294_, 0);
lean_dec(v_unused_1330_);
v___x_1301_ = v_a_1294_;
v_isShared_1302_ = v_isSharedCheck_1329_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_tail_1299_);
lean_dec(v_a_1294_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1329_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v_fst_1303_; lean_object* v_startPos_1304_; lean_object* v_stopPos_1305_; lean_object* v_startPos_1306_; lean_object* v_stopPos_1307_; lean_object* v_off_1308_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1323_; lean_object* v___x_1326_; uint8_t v_decide_1327_; 
v_fst_1303_ = lean_ctor_get(v_head_1297_, 0);
lean_inc(v_fst_1303_);
lean_dec(v_head_1297_);
v_startPos_1304_ = lean_ctor_get(v_snd_1298_, 1);
v_stopPos_1305_ = lean_ctor_get(v_snd_1298_, 2);
v_startPos_1306_ = lean_ctor_get(v_rawVal_1290_, 1);
v_stopPos_1307_ = lean_ctor_get(v_rawVal_1290_, 2);
v_off_1308_ = lean_nat_sub(v_startPos_1304_, v_startPos_1306_);
v___x_1326_ = lean_unsigned_to_nat(0u);
v_decide_1327_ = lean_nat_dec_eq(v_off_1308_, v___x_1326_);
if (v_decide_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1323_ = v___x_1328_;
goto v___jp_1322_;
}
else
{
lean_inc_ref(v_leading_1293_);
v___y_1323_ = v_leading_1293_;
goto v___jp_1322_;
}
v___jp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_info_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1312_ = lean_nat_add(v_off_1308_, v_pos_1291_);
lean_dec(v_off_1308_);
v___x_1313_ = lean_nat_sub(v_stopPos_1305_, v_startPos_1304_);
v___x_1314_ = lean_nat_add(v___x_1313_, v___x_1312_);
lean_dec(v___x_1313_);
v_info_1315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1315_, 0, v___y_1310_);
lean_ctor_set(v_info_1315_, 1, v___x_1312_);
lean_ctor_set(v_info_1315_, 2, v___y_1311_);
lean_ctor_set(v_info_1315_, 3, v___x_1314_);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1317_, 0, v_info_1315_);
lean_ctor_set(v___x_1317_, 1, v_snd_1298_);
lean_ctor_set(v___x_1317_, 2, v_fst_1303_);
lean_ctor_set(v___x_1317_, 3, v___x_1316_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v_a_1295_);
lean_ctor_set(v___x_1301_, 0, v___x_1317_);
v___x_1319_ = v___x_1301_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_a_1295_);
v___x_1319_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
v_a_1294_ = v_tail_1299_;
v_a_1295_ = v___x_1319_;
goto _start;
}
}
v___jp_1322_:
{
uint8_t v_decide_1324_; 
v_decide_1324_ = lean_nat_dec_eq(v_stopPos_1305_, v_stopPos_1307_);
if (v_decide_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1310_ = v___y_1323_;
v___y_1311_ = v___x_1325_;
goto v___jp_1309_;
}
else
{
lean_inc_ref(v_trailing_1292_);
v___y_1310_ = v___y_1323_;
v___y_1311_ = v_trailing_1292_;
goto v___jp_1309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1331_, lean_object* v_pos_1332_, lean_object* v_trailing_1333_, lean_object* v_leading_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1331_, v_pos_1332_, v_trailing_1333_, v_leading_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_pos_1332_);
lean_dec_ref(v_rawVal_1331_);
return v_res_1337_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__4(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1343_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1344_ = lean_unsigned_to_nat(9u);
v___x_1345_ = lean_unsigned_to_nat(342u);
v___x_1346_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1347_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1348_ = l_mkPanicMessageWithDecl(v___x_1347_, v___x_1346_, v___x_1345_, v___x_1344_, v___x_1343_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1349_, lean_object* v_nFields_x3f_1350_){
_start:
{
if (lean_obj_tag(v_stx_1349_) == 3)
{
lean_object* v_info_1351_; 
v_info_1351_ = lean_ctor_get(v_stx_1349_, 0);
lean_inc(v_info_1351_);
if (lean_obj_tag(v_info_1351_) == 0)
{
lean_object* v_rawVal_1352_; lean_object* v_val_1353_; lean_object* v_leading_1354_; lean_object* v_pos_1355_; lean_object* v_trailing_1356_; lean_object* v_rawComps_1357_; uint8_t v___x_1358_; 
v_rawVal_1352_ = lean_ctor_get(v_stx_1349_, 1);
lean_inc_ref_n(v_rawVal_1352_, 2);
v_val_1353_ = lean_ctor_get(v_stx_1349_, 2);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_stx_1349_, 4);
v_leading_1354_ = lean_ctor_get(v_info_1351_, 0);
lean_inc_ref(v_leading_1354_);
v_pos_1355_ = lean_ctor_get(v_info_1351_, 1);
lean_inc(v_pos_1355_);
v_trailing_1356_ = lean_ctor_get(v_info_1351_, 2);
lean_inc_ref(v_trailing_1356_);
lean_dec_ref_known(v_info_1351_, 4);
v_rawComps_1357_ = l_Lean_Syntax_splitNameLit(v_rawVal_1352_);
v___x_1358_ = l_List_isEmpty___redArg(v_rawComps_1357_);
if (v___x_1358_ == 0)
{
lean_object* v_val_1359_; lean_object* v_nameComps_1360_; lean_object* v___y_1362_; 
v_val_1359_ = l_Lean_Name_eraseMacroScopes(v_val_1353_);
lean_dec(v_val_1353_);
v_nameComps_1360_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1359_, v_nFields_x3f_1350_);
if (lean_obj_tag(v_nFields_x3f_1350_) == 1)
{
lean_object* v_val_1376_; lean_object* v_str_1377_; lean_object* v_startPos_1378_; lean_object* v_stopPos_1379_; lean_object* v___x_1380_; lean_object* v_nPrefix_1381_; lean_object* v___y_1383_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_prefixSz_1389_; lean_object* v___x_1390_; lean_object* v_prefixSz_1391_; lean_object* v___y_1393_; uint8_t v___x_1398_; 
v_val_1376_ = lean_ctor_get(v_nFields_x3f_1350_, 0);
v_str_1377_ = lean_ctor_get(v_rawVal_1352_, 0);
v_startPos_1378_ = lean_ctor_get(v_rawVal_1352_, 1);
v_stopPos_1379_ = lean_ctor_get(v_rawVal_1352_, 2);
v___x_1380_ = l_List_lengthTR___redArg(v_rawComps_1357_);
v_nPrefix_1381_ = lean_nat_sub(v___x_1380_, v_val_1376_);
lean_dec(v___x_1380_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1381_);
lean_inc(v_rawComps_1357_);
v___x_1388_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1357_, v_rawComps_1357_, v_nPrefix_1381_, v___x_1387_);
v_prefixSz_1389_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1386_, v___x_1388_);
lean_dec(v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(1u);
v_prefixSz_1391_ = lean_nat_sub(v_prefixSz_1389_, v___x_1390_);
lean_dec(v_prefixSz_1389_);
v___x_1398_ = lean_nat_dec_le(v_prefixSz_1391_, v___x_1386_);
if (v___x_1398_ == 0)
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_le(v_stopPos_1379_, v_startPos_1378_);
if (v___x_1399_ == 0)
{
lean_inc(v_startPos_1378_);
v___y_1393_ = v_startPos_1378_;
goto v___jp_1392_;
}
else
{
lean_inc(v_stopPos_1379_);
v___y_1393_ = v_stopPos_1379_;
goto v___jp_1392_;
}
}
else
{
lean_object* v___x_1400_; 
lean_dec(v_prefixSz_1391_);
v___x_1400_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1383_ = v___x_1400_;
goto v___jp_1382_;
}
v___jp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = l_List_drop___redArg(v_nPrefix_1381_, v_rawComps_1357_);
lean_dec(v_rawComps_1357_);
v___x_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___y_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___y_1362_ = v___x_1385_;
goto v___jp_1361_;
}
v___jp_1392_:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_nat_add(v_startPos_1378_, v_prefixSz_1391_);
lean_dec(v_prefixSz_1391_);
v___x_1395_ = lean_nat_dec_le(v_stopPos_1379_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_inc_ref(v_str_1377_);
v___x_1396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1396_, 0, v_str_1377_);
lean_ctor_set(v___x_1396_, 1, v___y_1393_);
lean_ctor_set(v___x_1396_, 2, v___x_1394_);
v___y_1383_ = v___x_1396_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1397_; 
lean_dec(v___x_1394_);
lean_inc(v_stopPos_1379_);
lean_inc_ref(v_str_1377_);
v___x_1397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1397_, 0, v_str_1377_);
lean_ctor_set(v___x_1397_, 1, v___y_1393_);
lean_ctor_set(v___x_1397_, 2, v_stopPos_1379_);
v___y_1383_ = v___x_1397_;
goto v___jp_1382_;
}
}
}
else
{
v___y_1362_ = v_rawComps_1357_;
goto v___jp_1361_;
}
v___jp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = l_List_lengthTR___redArg(v_nameComps_1360_);
v___x_1364_ = l_List_lengthTR___redArg(v___y_1362_);
v___x_1365_ = lean_nat_dec_eq(v___x_1363_, v___x_1364_);
lean_dec(v___x_1364_);
lean_dec(v___x_1363_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec(v___y_1362_);
lean_dec(v_nameComps_1360_);
lean_dec_ref(v_trailing_1356_);
lean_dec(v_pos_1355_);
lean_dec_ref(v_leading_1354_);
lean_dec_ref(v_rawVal_1352_);
v___x_1366_ = lean_box(0);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_comps_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_seps_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc(v___y_1362_);
v___x_1367_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1360_, v___y_1362_);
v___x_1368_ = lean_box(0);
v_comps_1369_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1352_, v_pos_1355_, v_trailing_1356_, v_leading_1354_, v___x_1367_, v___x_1368_);
v___x_1370_ = lean_array_mk(v___y_1362_);
v___x_1371_ = lean_array_pop(v___x_1370_);
v___x_1372_ = lean_array_to_list(v___x_1371_);
v_seps_1373_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1352_, v_pos_1355_, v___x_1372_, v___x_1368_);
lean_dec(v_pos_1355_);
lean_dec_ref(v_rawVal_1352_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_comps_1369_);
lean_ctor_set(v___x_1374_, 1, v_seps_1373_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
}
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_rawComps_1357_);
lean_dec_ref(v_trailing_1356_);
lean_dec(v_pos_1355_);
lean_dec_ref(v_leading_1354_);
lean_dec(v_val_1353_);
lean_dec_ref(v_rawVal_1352_);
v___x_1401_ = lean_box(0);
return v___x_1401_;
}
}
else
{
lean_object* v___x_1402_; 
lean_dec(v_info_1351_);
lean_dec_ref_known(v_stx_1349_, 4);
v___x_1402_ = lean_box(0);
return v___x_1402_;
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_stx_1349_);
v___x_1403_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__4, &l_Lean_Syntax_identComponents_x3f___closed__4_once, _init_l_Lean_Syntax_identComponents_x3f___closed__4);
v___x_1404_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1405_, lean_object* v_nFields_x3f_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Syntax_identComponents_x3f(v_stx_1405_, v_nFields_x3f_1406_);
lean_dec(v_nFields_x3f_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1408_, lean_object* v_nFields_x3f_1409_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1409_) == 1)
{
lean_object* v_val_1410_; lean_object* v_nameComps_1411_; lean_object* v___x_1412_; lean_object* v_nPrefix_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_namePrefix_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_val_1410_ = lean_ctor_get(v_nFields_x3f_1409_, 0);
v_nameComps_1411_ = l_Lean_Name_components(v_n_1408_);
v___x_1412_ = l_List_lengthTR___redArg(v_nameComps_1411_);
v_nPrefix_1413_ = lean_nat_sub(v___x_1412_, v_val_1410_);
lean_dec(v___x_1412_);
v___x_1414_ = lean_box(0);
v___x_1415_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1413_);
lean_inc(v_nameComps_1411_);
v___x_1416_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1411_, v_nameComps_1411_, v_nPrefix_1413_, v___x_1415_);
v_namePrefix_1417_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1414_, v___x_1416_);
v___x_1418_ = l_List_drop___redArg(v_nPrefix_1413_, v_nameComps_1411_);
lean_dec(v_nameComps_1411_);
v___x_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_namePrefix_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Name_components(v_n_1408_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1421_, lean_object* v_nFields_x3f_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1421_, v_nFields_x3f_1422_);
lean_dec(v_nFields_x3f_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_panic_fn_borrowed(v___x_1425_, v_msg_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_info_1427_);
v___x_1430_ = l_List_reverse___redArg(v_a_1429_);
return v___x_1430_;
}
else
{
lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1447_; 
v_head_1431_ = lean_ctor_get(v_a_1428_, 0);
v_tail_1432_ = lean_ctor_get(v_a_1428_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1434_ = v_a_1428_;
v_isShared_1435_ = v_isSharedCheck_1447_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_tail_1432_);
lean_inc(v_head_1431_);
lean_dec(v_a_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1447_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1436_ = 1;
lean_inc(v_head_1431_);
v___x_1437_ = l_Lean_Name_toString(v_head_1431_, v___x_1436_);
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_string_utf8_byte_size(v___x_1437_);
v___x_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1437_);
lean_ctor_set(v___x_1440_, 1, v___x_1438_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
v___x_1441_ = lean_box(0);
lean_inc(v_info_1427_);
v___x_1442_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1442_, 0, v_info_1427_);
lean_ctor_set(v___x_1442_, 1, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v_head_1431_);
lean_ctor_set(v___x_1442_, 3, v___x_1441_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_a_1429_);
lean_ctor_set(v___x_1434_, 0, v___x_1442_);
v___x_1444_ = v___x_1434_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1429_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v_a_1428_ = v_tail_1432_;
v_a_1429_ = v___x_1444_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1450_ = lean_unsigned_to_nat(9u);
v___x_1451_ = lean_unsigned_to_nat(377u);
v___x_1452_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1453_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1455_, lean_object* v_nFields_x3f_1456_){
_start:
{
if (lean_obj_tag(v_stx_1455_) == 3)
{
lean_object* v_info_1457_; lean_object* v_rawVal_1458_; lean_object* v_val_1459_; lean_object* v_val_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_info_1457_ = lean_ctor_get(v_stx_1455_, 0);
lean_inc(v_info_1457_);
v_rawVal_1458_ = lean_ctor_get(v_stx_1455_, 1);
v_val_1459_ = lean_ctor_get(v_stx_1455_, 2);
v_val_1460_ = l_Lean_Name_eraseMacroScopes(v_val_1459_);
v___x_1461_ = l_Lean_Name_getNumParts(v_val_1460_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_dec_le(v___x_1461_, v___x_1462_);
lean_dec(v___x_1461_);
if (v___x_1463_ == 0)
{
if (lean_obj_tag(v_info_1457_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Syntax_identComponents_x3f(v_stx_1455_, v_nFields_x3f_1456_);
if (lean_obj_tag(v___x_1464_) == 1)
{
lean_object* v_val_1465_; lean_object* v_fst_1466_; 
lean_dec_ref_known(v_info_1457_, 4);
lean_dec(v_val_1460_);
v_val_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v_fst_1466_ = lean_ctor_get(v_val_1465_, 0);
lean_inc(v_fst_1466_);
lean_dec(v_val_1465_);
return v_fst_1466_;
}
else
{
lean_object* v_nameComps_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v___x_1464_);
v_nameComps_1467_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1460_, v_nFields_x3f_1456_);
v___x_1468_ = lean_box(0);
v___x_1469_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1457_, v_nameComps_1467_, v___x_1468_);
return v___x_1469_;
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref_known(v_stx_1455_, 4);
v___x_1470_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1460_, v_nFields_x3f_1456_);
v___x_1471_ = lean_box(0);
v___x_1472_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1457_, v___x_1470_, v___x_1471_);
return v___x_1472_;
}
}
else
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1481_; 
lean_inc_ref(v_rawVal_1458_);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_stx_1455_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1482_ = lean_ctor_get(v_stx_1455_, 3);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_stx_1455_, 2);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_stx_1455_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_stx_1455_, 0);
lean_dec(v_unused_1485_);
v___x_1474_ = v_stx_1455_;
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_stx_1455_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_box(0);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 3, v___x_1476_);
lean_ctor_set(v___x_1474_, 2, v_val_1460_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_info_1457_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_rawVal_1458_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_val_1460_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1476_);
return v___x_1479_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v_stx_1455_);
v___x_1486_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1487_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1486_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1488_, lean_object* v_nFields_x3f_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Syntax_identComponents(v_stx_1488_, v_nFields_x3f_1489_);
lean_dec(v_nFields_x3f_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1491_, uint8_t v_firstChoiceOnly_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1493_, 0, v_stx_1491_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*1, v_firstChoiceOnly_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1494_, lean_object* v_firstChoiceOnly_1495_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1496_; lean_object* v_res_1497_; 
v_firstChoiceOnly_boxed_1496_ = lean_unbox(v_firstChoiceOnly_1495_);
v_res_1497_ = l_Lean_Syntax_topDown(v_stx_1494_, v_firstChoiceOnly_boxed_1496_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1498_, lean_object* v_____r_1499_, lean_object* v_b_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_b_1500_);
v___x_1502_ = lean_apply_2(v_toPure_1498_, lean_box(0), v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1503_, lean_object* v_toPure_1504_, lean_object* v_____s_1505_){
_start:
{
lean_object* v_fst_1506_; 
v_fst_1506_ = lean_ctor_get(v_____s_1505_, 0);
if (lean_obj_tag(v_fst_1506_) == 0)
{
lean_object* v_snd_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_toPure_1504_);
v_snd_1507_ = lean_ctor_get(v_____s_1505_, 1);
lean_inc(v_snd_1507_);
lean_dec_ref(v_____s_1505_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_apply_2(v___f_1503_, v___x_1508_, v_snd_1507_);
return v___x_1509_;
}
else
{
lean_object* v_val_1510_; lean_object* v___x_1511_; 
lean_inc_ref(v_fst_1506_);
lean_dec_ref(v_____s_1505_);
lean_dec(v___f_1503_);
v_val_1510_ = lean_ctor_get(v_fst_1506_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v_fst_1506_, 1);
v___x_1511_ = lean_apply_2(v_toPure_1504_, lean_box(0), v_val_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1512_, lean_object* v_toPure_1513_, lean_object* v___x_1514_, lean_object* v_____do__lift_1515_){
_start:
{
if (lean_obj_tag(v_____do__lift_1515_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v___x_1514_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_____do__lift_1515_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v_snd_1512_);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
v___x_1519_ = lean_apply_2(v_toPure_1513_, lean_box(0), v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_snd_1512_);
v_a_1520_ = lean_ctor_get(v_____do__lift_1515_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_____do__lift_1515_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1522_ = v_____do__lift_1515_;
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v_____do__lift_1515_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1514_);
lean_ctor_set(v___x_1524_, 1, v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_apply_2(v_toPure_1513_, lean_box(0), v___x_1526_);
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1530_, lean_object* v___x_1531_, lean_object* v_inst_1532_, lean_object* v_f_1533_, lean_object* v_firstChoiceOnly_1534_, lean_object* v_toBind_1535_, lean_object* v_a_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1539_; lean_object* v_res_1540_; 
v_firstChoiceOnly_boxed_1539_ = lean_unbox(v_firstChoiceOnly_1534_);
v_res_1540_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1530_, v___x_1531_, v_inst_1532_, v_f_1533_, v_firstChoiceOnly_boxed_1539_, v_toBind_1535_, v_a_1536_, v_x_1537_, v___y_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1544_, lean_object* v_stx_1545_, lean_object* v_inst_1546_, lean_object* v_f_1547_, uint8_t v_firstChoiceOnly_1548_, lean_object* v_toBind_1549_, lean_object* v___f_1550_, lean_object* v___x_1551_, lean_object* v___f_1552_, lean_object* v_____do__lift_1553_){
_start:
{
if (lean_obj_tag(v_____do__lift_1553_) == 0)
{
lean_object* v___x_1554_; 
lean_dec(v___f_1552_);
lean_dec(v___f_1550_);
lean_dec(v_toBind_1549_);
lean_dec(v_f_1547_);
lean_dec_ref(v_inst_1546_);
lean_dec(v_stx_1545_);
v___x_1554_ = lean_apply_2(v_toPure_1544_, lean_box(0), v_____do__lift_1553_);
return v___x_1554_;
}
else
{
if (lean_obj_tag(v_stx_1545_) == 1)
{
lean_object* v_a_1555_; lean_object* v_kind_1556_; lean_object* v_args_1557_; 
lean_dec(v___f_1552_);
v_a_1555_ = lean_ctor_get(v_____do__lift_1553_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v_____do__lift_1553_, 1);
v_kind_1556_ = lean_ctor_get(v_stx_1545_, 1);
lean_inc(v_kind_1556_);
v_args_1557_ = lean_ctor_get(v_stx_1545_, 2);
lean_inc_ref(v_args_1557_);
lean_dec_ref_known(v_stx_1545_, 3);
if (v_firstChoiceOnly_1548_ == 0)
{
lean_dec(v_kind_1556_);
goto v___jp_1558_;
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1568_ = lean_name_eq(v_kind_1556_, v___x_1567_);
lean_dec(v_kind_1556_);
if (v___x_1568_ == 0)
{
goto v___jp_1558_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v___f_1550_);
lean_dec(v_toBind_1549_);
lean_dec(v_toPure_1544_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_array_get(v___x_1551_, v_args_1557_, v___x_1569_);
lean_dec_ref(v_args_1557_);
v___x_1571_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1546_, v_f_1547_, v_firstChoiceOnly_1548_, v___x_1570_, v_a_1555_);
return v___x_1571_;
}
}
v___jp_1558_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; lean_object* v___x_1562_; size_t v_sz_1563_; size_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_box(v_firstChoiceOnly_1548_);
lean_inc(v_toBind_1549_);
lean_inc_ref(v_inst_1546_);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1561_, 0, v_toPure_1544_);
lean_closure_set(v___f_1561_, 1, v___x_1559_);
lean_closure_set(v___f_1561_, 2, v_inst_1546_);
lean_closure_set(v___f_1561_, 3, v_f_1547_);
lean_closure_set(v___f_1561_, 4, v___x_1560_);
lean_closure_set(v___f_1561_, 5, v_toBind_1549_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1559_);
lean_ctor_set(v___x_1562_, 1, v_a_1555_);
v_sz_1563_ = lean_array_size(v_args_1557_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1546_, v_args_1557_, v___f_1561_, v_sz_1563_, v___x_1564_, v___x_1562_);
v___x_1566_ = lean_apply_4(v_toBind_1549_, lean_box(0), lean_box(0), v___x_1565_, v___f_1550_);
return v___x_1566_;
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v___f_1550_);
lean_dec(v_toBind_1549_);
lean_dec(v_f_1547_);
lean_dec_ref(v_inst_1546_);
lean_dec(v_stx_1545_);
lean_dec(v_toPure_1544_);
v_a_1572_ = lean_ctor_get(v_____do__lift_1553_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v_____do__lift_1553_, 1);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_apply_2(v___f_1552_, v___x_1573_, v_a_1572_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1575_, lean_object* v_stx_1576_, lean_object* v_inst_1577_, lean_object* v_f_1578_, lean_object* v_firstChoiceOnly_1579_, lean_object* v_toBind_1580_, lean_object* v___f_1581_, lean_object* v___x_1582_, lean_object* v___f_1583_, lean_object* v_____do__lift_1584_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1585_; lean_object* v_res_1586_; 
v_firstChoiceOnly_boxed_1585_ = lean_unbox(v_firstChoiceOnly_1579_);
v_res_1586_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1575_, v_stx_1576_, v_inst_1577_, v_f_1578_, v_firstChoiceOnly_boxed_1585_, v_toBind_1580_, v___f_1581_, v___x_1582_, v___f_1583_, v_____do__lift_1584_);
lean_dec(v___x_1582_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1587_, lean_object* v_f_1588_, uint8_t v_firstChoiceOnly_1589_, lean_object* v_stx_1590_, lean_object* v_b_1591_){
_start:
{
lean_object* v_toApplicative_1592_; lean_object* v_toBind_1593_; lean_object* v_toPure_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___f_1600_; lean_object* v___x_1601_; 
v_toApplicative_1592_ = lean_ctor_get(v_inst_1587_, 0);
v_toBind_1593_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc_n(v_toBind_1593_, 2);
v_toPure_1594_ = lean_ctor_get(v_toApplicative_1592_, 1);
lean_inc_n(v_toPure_1594_, 3);
v___x_1595_ = lean_box(0);
lean_inc(v_f_1588_);
lean_inc(v_stx_1590_);
v___x_1596_ = lean_apply_2(v_f_1588_, v_stx_1590_, v_b_1591_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1597_, 0, v_toPure_1594_);
lean_inc_ref(v___f_1597_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1598_, 0, v___f_1597_);
lean_closure_set(v___f_1598_, 1, v_toPure_1594_);
v___x_1599_ = lean_box(v_firstChoiceOnly_1589_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1600_, 0, v_toPure_1594_);
lean_closure_set(v___f_1600_, 1, v_stx_1590_);
lean_closure_set(v___f_1600_, 2, v_inst_1587_);
lean_closure_set(v___f_1600_, 3, v_f_1588_);
lean_closure_set(v___f_1600_, 4, v___x_1599_);
lean_closure_set(v___f_1600_, 5, v_toBind_1593_);
lean_closure_set(v___f_1600_, 6, v___f_1598_);
lean_closure_set(v___f_1600_, 7, v___x_1595_);
lean_closure_set(v___f_1600_, 8, v___f_1597_);
v___x_1601_ = lean_apply_4(v_toBind_1593_, lean_box(0), lean_box(0), v___x_1596_, v___f_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1602_, lean_object* v___x_1603_, lean_object* v_inst_1604_, lean_object* v_f_1605_, uint8_t v_firstChoiceOnly_1606_, lean_object* v_toBind_1607_, lean_object* v_a_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_snd_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_snd_1611_ = lean_ctor_get(v___y_1610_, 1);
lean_inc_n(v_snd_1611_, 2);
lean_dec_ref(v___y_1610_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1612_, 0, v_snd_1611_);
lean_closure_set(v___f_1612_, 1, v_toPure_1602_);
lean_closure_set(v___f_1612_, 2, v___x_1603_);
v___x_1613_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1604_, v_f_1605_, v_firstChoiceOnly_1606_, v_a_1608_, v_snd_1611_);
v___x_1614_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1613_, v___f_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1615_, lean_object* v_f_1616_, lean_object* v_firstChoiceOnly_1617_, lean_object* v_stx_1618_, lean_object* v_b_1619_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1620_; lean_object* v_res_1621_; 
v_firstChoiceOnly_boxed_1620_ = lean_unbox(v_firstChoiceOnly_1617_);
v_res_1621_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1615_, v_f_1616_, v_firstChoiceOnly_boxed_1620_, v_stx_1618_, v_b_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1622_, lean_object* v_inst_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_f_1625_, uint8_t v_firstChoiceOnly_1626_, lean_object* v_stx_1627_, lean_object* v_b_1628_, lean_object* v_inst_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1623_, v_f_1625_, v_firstChoiceOnly_1626_, v_stx_1627_, v_b_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1631_, lean_object* v_inst_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_f_1634_, lean_object* v_firstChoiceOnly_1635_, lean_object* v_stx_1636_, lean_object* v_b_1637_, lean_object* v_inst_1638_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1639_; lean_object* v_res_1640_; 
v_firstChoiceOnly_boxed_1639_ = lean_unbox(v_firstChoiceOnly_1635_);
v_res_1640_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1631_, v_inst_1632_, v_00_u03b2_1633_, v_f_1634_, v_firstChoiceOnly_boxed_1639_, v_stx_1636_, v_b_1637_, v_inst_1638_);
lean_dec(v_inst_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1641_, lean_object* v_____do__lift_1642_){
_start:
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v_____do__lift_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v_____do__lift_1642_);
v___x_1644_ = lean_apply_2(v_toPure_1641_, lean_box(0), v_a_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1645_, lean_object* v_toBind_1646_, lean_object* v___f_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_x_1649_, lean_object* v_init_1650_, lean_object* v_f_1651_){
_start:
{
uint8_t v_firstChoiceOnly_1652_; lean_object* v_stx_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_firstChoiceOnly_1652_ = lean_ctor_get_uint8(v_x_1649_, sizeof(void*)*1);
v_stx_1653_ = lean_ctor_get(v_x_1649_, 0);
lean_inc(v_stx_1653_);
lean_dec_ref(v_x_1649_);
v___x_1654_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1645_, v_f_1651_, v_firstChoiceOnly_1652_, v_stx_1653_, v_init_1650_);
v___x_1655_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v___x_1654_, v___f_1647_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1656_){
_start:
{
lean_object* v_toApplicative_1657_; lean_object* v_toBind_1658_; lean_object* v_toPure_1659_; lean_object* v___f_1660_; lean_object* v___f_1661_; 
v_toApplicative_1657_ = lean_ctor_get(v_inst_1656_, 0);
v_toBind_1658_ = lean_ctor_get(v_inst_1656_, 1);
lean_inc(v_toBind_1658_);
v_toPure_1659_ = lean_ctor_get(v_toApplicative_1657_, 1);
lean_inc(v_toPure_1659_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1660_, 0, v_toPure_1659_);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1661_, 0, v_inst_1656_);
lean_closure_set(v___f_1661_, 1, v_toBind_1658_);
lean_closure_set(v___f_1661_, 2, v___f_1660_);
return v___f_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1662_, lean_object* v_inst_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1666_, lean_object* v_val_1667_){
_start:
{
if (lean_obj_tag(v_info_1666_) == 0)
{
lean_object* v_leading_1668_; lean_object* v_trailing_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_leading_1668_ = lean_ctor_get(v_info_1666_, 0);
lean_inc_ref(v_leading_1668_);
v_trailing_1669_ = lean_ctor_get(v_info_1666_, 2);
lean_inc_ref(v_trailing_1669_);
lean_dec_ref_known(v_info_1666_, 4);
v___x_1670_ = lean_substring_tostring(v_leading_1668_);
v___x_1671_ = lean_string_append(v___x_1670_, v_val_1667_);
v___x_1672_ = lean_substring_tostring(v_trailing_1669_);
v___x_1673_ = lean_string_append(v___x_1671_, v___x_1672_);
lean_dec_ref(v___x_1672_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v_info_1666_);
v___x_1674_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1675_ = lean_string_append(v___x_1674_, v_val_1667_);
v___x_1676_ = lean_string_append(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1677_, lean_object* v_val_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1677_, v_val_1678_);
lean_dec_ref(v_val_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1680_, lean_object* v_as_1681_, size_t v_sz_1682_, size_t v_i_1683_, lean_object* v_b_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1683_, v_sz_1682_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_b_1684_);
return v___x_1686_;
}
else
{
lean_object* v_snd_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1714_; 
v_snd_1687_ = lean_ctor_get(v_b_1684_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_b_1684_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_b_1684_, 0);
lean_dec(v_unused_1715_);
v___x_1689_ = v_b_1684_;
v_isShared_1690_ = v_isSharedCheck_1714_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_snd_1687_);
lean_dec(v_b_1684_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1714_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_array_uget_borrowed(v_as_1681_, v_i_1683_);
lean_inc(v_snd_1687_);
lean_inc(v_a_1691_);
v___x_1692_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1680_, v_a_1691_, v_snd_1687_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v___x_1693_; 
lean_del_object(v___x_1689_);
lean_dec(v_snd_1687_);
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
else
{
lean_object* v_val_1694_; 
v_val_1694_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_val_1694_);
if (lean_obj_tag(v_val_1694_) == 0)
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1704_; 
v_isSharedCheck_1704_ = !lean_is_exclusive(v_val_1694_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v_val_1694_, 0);
lean_dec(v_unused_1705_);
v___x_1696_ = v_val_1694_;
v_isShared_1697_ = v_isSharedCheck_1704_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v_val_1694_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1704_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1692_);
v___x_1699_ = v___x_1689_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_snd_1687_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 1);
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1692_, 1);
lean_dec(v_snd_1687_);
v_a_1706_ = lean_ctor_get(v_val_1694_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v_val_1694_, 1);
v___x_1707_ = lean_box(0);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v_a_1706_);
lean_ctor_set(v___x_1689_, 0, v___x_1707_);
v___x_1709_ = v___x_1689_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_a_1706_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
size_t v___x_1710_; size_t v___x_1711_; 
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1683_, v___x_1710_);
v_i_1683_ = v___x_1711_;
v_b_1684_ = v___x_1709_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_){
_start:
{
lean_object* v_array_1719_; lean_object* v_start_1720_; lean_object* v_stop_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1740_; 
v_array_1719_ = lean_ctor_get(v_a_1717_, 0);
v_start_1720_ = lean_ctor_get(v_a_1717_, 1);
v_stop_1721_ = lean_ctor_get(v_a_1717_, 2);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_a_1717_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1723_ = v_a_1717_;
v_isShared_1724_ = v_isSharedCheck_1740_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_stop_1721_);
lean_inc(v_start_1720_);
lean_inc(v_array_1719_);
lean_dec(v_a_1717_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1740_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_lt(v_start_1720_, v_stop_1721_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
lean_del_object(v___x_1723_);
lean_dec(v_stop_1721_);
lean_dec(v_start_1720_);
lean_dec_ref(v_array_1719_);
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_b_1718_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_array_fget_borrowed(v_array_1719_, v_start_1720_);
lean_inc(v___x_1727_);
v___x_1728_ = l_Lean_Syntax_reprint(v___x_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_del_object(v___x_1723_);
lean_dec(v_stop_1721_);
lean_dec(v_start_1720_);
lean_dec_ref(v_array_1719_);
v___x_1729_ = lean_box(0);
return v___x_1729_;
}
else
{
lean_object* v_val_1730_; uint8_t v___x_1731_; 
v_val_1730_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1731_ = lean_string_dec_eq(v_val_1716_, v_val_1730_);
lean_dec(v_val_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_del_object(v___x_1723_);
lean_dec(v_stop_1721_);
lean_dec(v_start_1720_);
lean_dec_ref(v_array_1719_);
v___x_1732_ = lean_box(0);
return v___x_1732_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1733_ = lean_box(0);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_start_1720_, v___x_1734_);
lean_dec(v_start_1720_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1735_);
v___x_1737_ = v___x_1723_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_array_1719_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_stop_1721_);
v___x_1737_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
v_a_1717_ = v___x_1737_;
v_b_1718_ = v___x_1733_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1741_, lean_object* v_stx_1742_, lean_object* v_b_1743_){
_start:
{
lean_object* v_b_1745_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___x_1759_; lean_object* v_a_1761_; 
v___x_1759_ = lean_box(0);
switch(lean_obj_tag(v_stx_1742_))
{
case 2:
{
lean_object* v_info_1770_; lean_object* v_val_1771_; lean_object* v___x_1772_; lean_object* v_s_1773_; 
v_info_1770_ = lean_ctor_get(v_stx_1742_, 0);
v_val_1771_ = lean_ctor_get(v_stx_1742_, 1);
lean_inc(v_info_1770_);
v___x_1772_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1770_, v_val_1771_);
v_s_1773_ = lean_string_append(v_b_1743_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v_a_1761_ = v_s_1773_;
goto v___jp_1760_;
}
case 3:
{
lean_object* v_rawVal_1774_; lean_object* v_info_1775_; lean_object* v_str_1776_; lean_object* v_startPos_1777_; lean_object* v_stopPos_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_s_1781_; 
v_rawVal_1774_ = lean_ctor_get(v_stx_1742_, 1);
v_info_1775_ = lean_ctor_get(v_stx_1742_, 0);
v_str_1776_ = lean_ctor_get(v_rawVal_1774_, 0);
v_startPos_1777_ = lean_ctor_get(v_rawVal_1774_, 1);
v_stopPos_1778_ = lean_ctor_get(v_rawVal_1774_, 2);
v___x_1779_ = lean_string_utf8_extract(v_str_1776_, v_startPos_1777_, v_stopPos_1778_);
lean_inc(v_info_1775_);
v___x_1780_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1775_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v_s_1781_ = lean_string_append(v_b_1743_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v_a_1761_ = v_s_1781_;
goto v___jp_1760_;
}
case 1:
{
lean_object* v_kind_1782_; lean_object* v_args_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_kind_1782_ = lean_ctor_get(v_stx_1742_, 1);
v_args_1783_ = lean_ctor_get(v_stx_1742_, 2);
v___x_1784_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1785_ = lean_name_eq(v_kind_1782_, v___x_1784_);
if (v___x_1785_ == 0)
{
v_a_1761_ = v_b_1743_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_array_get_borrowed(v___x_1759_, v_args_1783_, v___x_1786_);
lean_inc(v___x_1787_);
v___x_1788_ = l_Lean_Syntax_reprint(v___x_1787_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v___x_1789_; 
lean_dec_ref_known(v_stx_1742_, 3);
lean_dec_ref(v_b_1743_);
v___x_1789_ = lean_box(0);
return v___x_1789_;
}
else
{
lean_object* v_val_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_val_1790_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1790_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = lean_array_get_size(v_args_1783_);
lean_inc_ref(v_args_1783_);
v___x_1793_ = l_Array_toSubarray___redArg(v_args_1783_, v___x_1791_, v___x_1792_);
v___x_1794_ = lean_box(0);
v___x_1795_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1790_, v___x_1793_, v___x_1794_);
lean_dec(v_val_1790_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v___x_1796_; 
lean_dec_ref_known(v_stx_1742_, 3);
lean_dec_ref(v_b_1743_);
v___x_1796_ = lean_box(0);
return v___x_1796_;
}
else
{
lean_dec_ref_known(v___x_1795_, 1);
v_a_1761_ = v_b_1743_;
goto v___jp_1760_;
}
}
}
}
default: 
{
v_a_1761_ = v_b_1743_;
goto v___jp_1760_;
}
}
v___jp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1745_);
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
v___jp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; size_t v_sz_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___y_1750_);
v_sz_1753_ = lean_array_size(v___y_1749_);
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1741_, v___y_1749_, v_sz_1753_, v___x_1754_, v___x_1752_);
lean_dec_ref(v___y_1749_);
if (lean_obj_tag(v___x_1755_) == 0)
{
return v___x_1751_;
}
else
{
lean_object* v_val_1756_; lean_object* v_fst_1757_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v_fst_1757_ = lean_ctor_get(v_val_1756_, 0);
if (lean_obj_tag(v_fst_1757_) == 0)
{
lean_object* v_snd_1758_; 
v_snd_1758_ = lean_ctor_get(v_val_1756_, 1);
lean_inc(v_snd_1758_);
lean_dec(v_val_1756_);
v_b_1745_ = v_snd_1758_;
goto v___jp_1744_;
}
else
{
lean_inc_ref(v_fst_1757_);
lean_dec(v_val_1756_);
return v_fst_1757_;
}
}
}
v___jp_1760_:
{
if (lean_obj_tag(v_stx_1742_) == 1)
{
if (v_firstChoiceOnly_1741_ == 0)
{
lean_object* v_args_1762_; 
v_args_1762_ = lean_ctor_get(v_stx_1742_, 2);
lean_inc_ref(v_args_1762_);
lean_dec_ref_known(v_stx_1742_, 3);
v___y_1749_ = v_args_1762_;
v___y_1750_ = v_a_1761_;
goto v___jp_1748_;
}
else
{
lean_object* v_kind_1763_; lean_object* v_args_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_kind_1763_ = lean_ctor_get(v_stx_1742_, 1);
lean_inc(v_kind_1763_);
v_args_1764_ = lean_ctor_get(v_stx_1742_, 2);
lean_inc_ref(v_args_1764_);
lean_dec_ref_known(v_stx_1742_, 3);
v___x_1765_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1766_ = lean_name_eq(v_kind_1763_, v___x_1765_);
lean_dec(v_kind_1763_);
if (v___x_1766_ == 0)
{
v___y_1749_ = v_args_1764_;
v___y_1750_ = v_a_1761_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_array_get(v___x_1759_, v_args_1764_, v___x_1767_);
lean_dec_ref(v_args_1764_);
v_stx_1742_ = v___x_1768_;
v_b_1743_ = v_a_1761_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1742_);
v_b_1745_ = v_a_1761_;
goto v___jp_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1797_){
_start:
{
lean_object* v_s_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; 
v_s_1798_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1799_ = 1;
v___x_1800_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1799_, v_stx_1797_, v_s_1798_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_box(0);
return v___x_1801_;
}
else
{
lean_object* v_val_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1810_; 
v_val_1802_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1804_ = v___x_1800_;
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_val_1802_);
lean_dec(v___x_1800_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_a_1806_; lean_object* v___x_1808_; 
v_a_1806_ = lean_ctor_get(v_val_1802_, 0);
lean_inc(v_a_1806_);
lean_dec(v_val_1802_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_a_1806_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1811_, v_a_1812_, v_b_1813_);
lean_dec_ref(v_val_1811_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1815_, lean_object* v_as_1816_, lean_object* v_sz_1817_, lean_object* v_i_1818_, lean_object* v_b_1819_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1820_; size_t v_sz_boxed_1821_; size_t v_i_boxed_1822_; lean_object* v_res_1823_; 
v_firstChoiceOnly_boxed_1820_ = lean_unbox(v_firstChoiceOnly_1815_);
v_sz_boxed_1821_ = lean_unbox_usize(v_sz_1817_);
lean_dec(v_sz_1817_);
v_i_boxed_1822_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1820_, v_as_1816_, v_sz_boxed_1821_, v_i_boxed_1822_, v_b_1819_);
lean_dec_ref(v_as_1816_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1824_, lean_object* v_stx_1825_, lean_object* v_b_1826_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1827_; lean_object* v_res_1828_; 
v_firstChoiceOnly_boxed_1827_ = lean_unbox(v_firstChoiceOnly_1824_);
v_res_1828_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1827_, v_stx_1825_, v_b_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1829_, lean_object* v_inst_1830_, lean_object* v_R_1831_, lean_object* v_a_1832_, lean_object* v_b_1833_, lean_object* v_c_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1829_, v_a_1832_, v_b_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1836_, lean_object* v_inst_1837_, lean_object* v_R_1838_, lean_object* v_a_1839_, lean_object* v_b_1840_, lean_object* v_c_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1836_, v_inst_1837_, v_R_1838_, v_a_1839_, v_b_1840_, v_c_1841_);
lean_dec_ref(v_val_1836_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1851_, lean_object* v_stx_1852_){
_start:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = l_Lean_Syntax_isMissing(v_stx_1852_);
if (v___x_1854_ == 0)
{
if (lean_obj_tag(v_stx_1852_) == 1)
{
lean_object* v_kind_1855_; lean_object* v_args_1856_; 
v_kind_1855_ = lean_ctor_get(v_stx_1852_, 1);
v_args_1856_ = lean_ctor_get(v_stx_1852_, 2);
if (v_firstChoiceOnly_1851_ == 0)
{
goto v___jp_1857_;
}
else
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1867_ = lean_name_eq(v_kind_1855_, v___x_1866_);
if (v___x_1867_ == 0)
{
goto v___jp_1857_;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_array_get_borrowed(v___x_1868_, v_args_1856_, v___x_1869_);
v_stx_1852_ = v___x_1870_;
goto _start;
}
}
v___jp_1857_:
{
lean_object* v___x_1858_; size_t v_sz_1859_; size_t v___x_1860_; lean_object* v___x_1861_; lean_object* v_fst_1862_; 
v___x_1858_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1859_ = lean_array_size(v_args_1856_);
v___x_1860_ = ((size_t)0ULL);
v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1851_, v_args_1856_, v_sz_1859_, v___x_1860_, v___x_1858_);
v_fst_1862_ = lean_ctor_get(v___x_1861_, 0);
if (lean_obj_tag(v_fst_1862_) == 0)
{
lean_object* v_snd_1863_; lean_object* v___x_1864_; 
v_snd_1863_ = lean_ctor_get(v___x_1861_, 1);
lean_inc(v_snd_1863_);
lean_dec_ref(v___x_1861_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_snd_1863_);
return v___x_1864_;
}
else
{
lean_object* v_val_1865_; 
lean_inc_ref(v_fst_1862_);
lean_dec_ref(v___x_1861_);
v_val_1865_ = lean_ctor_get(v_fst_1862_, 0);
lean_inc(v_val_1865_);
lean_dec_ref_known(v_fst_1862_, 1);
return v_val_1865_;
}
}
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1872_;
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = lean_box(v___x_1854_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1853_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1877_, lean_object* v_as_1878_, size_t v_sz_1879_, size_t v_i_1880_, lean_object* v_b_1881_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_usize_dec_lt(v_i_1880_, v_sz_1879_);
if (v___x_1882_ == 0)
{
return v_b_1881_;
}
else
{
lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1901_; 
v_snd_1883_ = lean_ctor_get(v_b_1881_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_b_1881_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_b_1881_, 0);
lean_dec(v_unused_1902_);
v___x_1885_ = v_b_1881_;
v_isShared_1886_ = v_isSharedCheck_1901_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_dec(v_b_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1901_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_a_1887_; lean_object* v___x_1888_; 
v_a_1887_ = lean_array_uget_borrowed(v_as_1878_, v_i_1880_);
v___x_1888_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1877_, v_a_1887_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1889_);
v___x_1891_ = v___x_1885_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_snd_1883_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec(v_snd_1883_);
v_a_1893_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1894_ = lean_box(0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_a_1893_);
lean_ctor_set(v___x_1885_, 0, v___x_1894_);
v___x_1896_ = v___x_1885_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_a_1893_);
v___x_1896_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
size_t v___x_1897_; size_t v___x_1898_; 
v___x_1897_ = ((size_t)1ULL);
v___x_1898_ = lean_usize_add(v_i_1880_, v___x_1897_);
v_i_1880_ = v___x_1898_;
v_b_1881_ = v___x_1896_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1903_, lean_object* v_as_1904_, lean_object* v_sz_1905_, lean_object* v_i_1906_, lean_object* v_b_1907_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1908_; size_t v_sz_boxed_1909_; size_t v_i_boxed_1910_; lean_object* v_res_1911_; 
v_firstChoiceOnly_boxed_1908_ = lean_unbox(v_firstChoiceOnly_1903_);
v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1905_);
lean_dec(v_sz_1905_);
v_i_boxed_1910_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1908_, v_as_1904_, v_sz_boxed_1909_, v_i_boxed_1910_, v_b_1907_);
lean_dec_ref(v_as_1904_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1912_, lean_object* v_stx_1913_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1914_; lean_object* v_res_1915_; 
v_firstChoiceOnly_boxed_1914_ = lean_unbox(v_firstChoiceOnly_1912_);
v_res_1915_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1914_, v_stx_1913_);
lean_dec(v_stx_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1916_){
_start:
{
uint8_t v___x_1917_; lean_object* v___y_1919_; lean_object* v___x_1923_; lean_object* v_a_1924_; 
v___x_1917_ = 0;
v___x_1923_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1917_, v_stx_1916_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___y_1919_ = v_a_1924_;
goto v___jp_1918_;
v___jp_1918_:
{
lean_object* v_fst_1920_; 
v_fst_1920_ = lean_ctor_get(v___y_1919_, 0);
lean_inc(v_fst_1920_);
lean_dec_ref(v___y_1919_);
if (lean_obj_tag(v_fst_1920_) == 0)
{
return v___x_1917_;
}
else
{
lean_object* v_val_1921_; uint8_t v___x_1922_; 
v_val_1921_ = lean_ctor_get(v_fst_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v_fst_1920_, 1);
v___x_1922_ = lean_unbox(v_val_1921_);
lean_dec(v_val_1921_);
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1925_){
_start:
{
uint8_t v_res_1926_; lean_object* v_r_1927_; 
v_res_1926_ = l_Lean_Syntax_hasMissing(v_stx_1925_);
lean_dec(v_stx_1925_);
v_r_1927_ = lean_box(v_res_1926_);
return v_r_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1928_, lean_object* v_stx_1929_, lean_object* v_b_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1928_, v_stx_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1932_, lean_object* v_stx_1933_, lean_object* v_b_1934_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1935_; lean_object* v_res_1936_; 
v_firstChoiceOnly_boxed_1935_ = lean_unbox(v_firstChoiceOnly_1932_);
v_res_1936_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1935_, v_stx_1933_, v_b_1934_);
lean_dec_ref(v_b_1934_);
lean_dec(v_stx_1933_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1937_, uint8_t v_canonicalOnly_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_Syntax_getPos_x3f(v_stx_1937_, v_canonicalOnly_1938_);
if (lean_obj_tag(v___x_1939_) == 1)
{
lean_object* v_val_1940_; lean_object* v___x_1941_; 
v_val_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_val_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1937_, v_canonicalOnly_1938_);
if (lean_obj_tag(v___x_1941_) == 1)
{
lean_object* v_val_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1950_; 
v_val_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_val_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_val_1940_);
lean_ctor_set(v___x_1946_, 1, v_val_1942_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_object* v___x_1951_; 
lean_dec(v___x_1941_);
lean_dec(v_val_1940_);
v___x_1951_ = lean_box(0);
return v___x_1951_;
}
}
else
{
lean_object* v___x_1952_; 
lean_dec(v___x_1939_);
v___x_1952_ = lean_box(0);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1953_, lean_object* v_canonicalOnly_1954_){
_start:
{
uint8_t v_canonicalOnly_boxed_1955_; lean_object* v_res_1956_; 
v_canonicalOnly_boxed_1955_ = lean_unbox(v_canonicalOnly_1954_);
v_res_1956_ = l_Lean_Syntax_getRange_x3f(v_stx_1953_, v_canonicalOnly_boxed_1955_);
lean_dec(v_stx_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1957_, uint8_t v_canonicalOnly_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_Syntax_getPos_x3f(v_stx_1957_, v_canonicalOnly_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_box(0);
return v___x_1960_;
}
else
{
lean_object* v_val_1961_; lean_object* v___x_1962_; 
v_val_1961_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_val_1961_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1962_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1957_, v_canonicalOnly_1958_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; 
lean_dec(v_val_1961_);
v___x_1963_ = lean_box(0);
return v___x_1963_;
}
else
{
lean_object* v_val_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_val_1964_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v___x_1962_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_val_1964_);
lean_dec(v___x_1962_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_val_1961_);
lean_ctor_set(v___x_1968_, 1, v_val_1964_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1973_, lean_object* v_canonicalOnly_1974_){
_start:
{
uint8_t v_canonicalOnly_boxed_1975_; lean_object* v_res_1976_; 
v_canonicalOnly_boxed_1975_ = lean_unbox(v_canonicalOnly_1974_);
v_res_1976_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1973_, v_canonicalOnly_boxed_1975_);
lean_dec(v_stx_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1977_, uint8_t v_canonical_1978_){
_start:
{
lean_object* v_start_1979_; lean_object* v_stop_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1989_; 
v_start_1979_ = lean_ctor_get(v_range_1977_, 0);
v_stop_1980_ = lean_ctor_get(v_range_1977_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_range_1977_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1982_ = v_range_1977_;
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_stop_1980_);
lean_inc(v_start_1979_);
lean_dec(v_range_1977_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1984_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1984_, 0, v_start_1979_);
lean_ctor_set(v___x_1984_, 1, v_stop_1980_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2, v_canonical_1978_);
v___x_1985_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 2);
lean_ctor_set(v___x_1982_, 1, v___x_1985_);
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1987_ = v___x_1982_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_1990_, lean_object* v_canonical_1991_){
_start:
{
uint8_t v_canonical_boxed_1992_; lean_object* v_res_1993_; 
v_canonical_boxed_1992_ = lean_unbox(v_canonical_1991_);
v_res_1993_ = l_Lean_Syntax_ofRange(v_range_1990_, v_canonical_boxed_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_1998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1998_, 0, v_stx_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
lean_ctor_set(v___x_1998_, 2, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_1999_, lean_object* v_stx_2000_){
_start:
{
lean_object* v_parents_2001_; lean_object* v_idxs_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_parents_2001_ = lean_ctor_get(v_t_1999_, 1);
v_idxs_2002_ = lean_ctor_get(v_t_1999_, 2);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_t_1999_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_t_1999_, 0);
lean_dec(v_unused_2010_);
v___x_2004_ = v_t_1999_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_idxs_2002_);
lean_inc(v_parents_2001_);
lean_dec(v_t_1999_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v_stx_2000_);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_stx_2000_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_parents_2001_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_idxs_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2011_, lean_object* v_idx_2012_){
_start:
{
lean_object* v_cur_2013_; lean_object* v_parents_2014_; lean_object* v_idxs_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2035_; 
v_cur_2013_ = lean_ctor_get(v_t_2011_, 0);
v_parents_2014_ = lean_ctor_get(v_t_2011_, 1);
v_idxs_2015_ = lean_ctor_get(v_t_2011_, 2);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_t_2011_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2017_ = v_t_2011_;
v_isShared_2018_ = v_isSharedCheck_2035_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_idxs_2015_);
lean_inc(v_parents_2014_);
lean_inc(v_cur_2013_);
lean_dec(v_t_2011_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2035_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = l_Lean_Syntax_getNumArgs(v_cur_2013_);
v___x_2020_ = lean_nat_dec_lt(v_idx_2012_, v___x_2019_);
lean_dec(v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_array_push(v_parents_2014_, v_cur_2013_);
v___x_2023_ = lean_array_push(v_idxs_2015_, v_idx_2012_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 2, v___x_2023_);
lean_ctor_set(v___x_2017_, 1, v___x_2022_);
lean_ctor_set(v___x_2017_, 0, v___x_2021_);
v___x_2025_ = v___x_2017_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2027_ = l_Lean_Syntax_getArg(v_cur_2013_, v_idx_2012_);
v___x_2028_ = lean_box(0);
v___x_2029_ = l_Lean_Syntax_setArg(v_cur_2013_, v_idx_2012_, v___x_2028_);
v___x_2030_ = lean_array_push(v_parents_2014_, v___x_2029_);
v___x_2031_ = lean_array_push(v_idxs_2015_, v_idx_2012_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 2, v___x_2031_);
lean_ctor_set(v___x_2017_, 1, v___x_2030_);
lean_ctor_set(v___x_2017_, 0, v___x_2027_);
v___x_2033_ = v___x_2017_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2036_){
_start:
{
lean_object* v_cur_2037_; lean_object* v_parents_2038_; lean_object* v_idxs_2039_; lean_object* v___y_2041_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_cur_2037_ = lean_ctor_get(v_t_2036_, 0);
v_parents_2038_ = lean_ctor_get(v_t_2036_, 1);
v_idxs_2039_ = lean_ctor_get(v_t_2036_, 2);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_array_get_size(v_parents_2038_);
v___x_2047_ = lean_nat_dec_lt(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
return v_t_2036_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
lean_inc_ref(v_idxs_2039_);
lean_inc_ref(v_parents_2038_);
lean_inc(v_cur_2037_);
lean_dec_ref(v_t_2036_);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_array_get_size(v_idxs_2039_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_sub(v___x_2049_, v___x_2050_);
v___x_2052_ = lean_array_get_borrowed(v___x_2045_, v_idxs_2039_, v___x_2051_);
lean_dec(v___x_2051_);
v___x_2053_ = lean_nat_sub(v___x_2046_, v___x_2050_);
v___x_2054_ = lean_array_get_borrowed(v___x_2048_, v_parents_2038_, v___x_2053_);
lean_dec(v___x_2053_);
v___x_2055_ = l_Lean_Syntax_getNumArgs(v___x_2054_);
v___x_2056_ = lean_nat_dec_lt(v___x_2052_, v___x_2055_);
lean_dec(v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec(v_cur_2037_);
lean_inc(v___x_2054_);
v___y_2041_ = v___x_2054_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2057_; 
lean_inc(v___x_2054_);
v___x_2057_ = l_Lean_Syntax_setArg(v___x_2054_, v___x_2052_, v_cur_2037_);
v___y_2041_ = v___x_2057_;
goto v___jp_2040_;
}
}
v___jp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = lean_array_pop(v_parents_2038_);
v___x_2043_ = lean_array_pop(v_idxs_2039_);
v___x_2044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2044_, 0, v___y_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2042_);
lean_ctor_set(v___x_2044_, 2, v___x_2043_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2058_){
_start:
{
lean_object* v_parents_2059_; lean_object* v_idxs_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_parents_2059_ = lean_ctor_get(v_t_2058_, 1);
v_idxs_2060_ = lean_ctor_get(v_t_2058_, 2);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_array_get_size(v_parents_2059_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
return v_t_2058_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_inc_ref(v_idxs_2060_);
v___x_2064_ = l_Lean_Syntax_Traverser_up(v_t_2058_);
v___x_2065_ = lean_array_get_size(v_idxs_2060_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_sub(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_array_get(v___x_2061_, v_idxs_2060_, v___x_2067_);
lean_dec(v___x_2067_);
lean_dec_ref(v_idxs_2060_);
v___x_2069_ = lean_nat_sub(v___x_2068_, v___x_2066_);
lean_dec(v___x_2068_);
v___x_2070_ = l_Lean_Syntax_Traverser_down(v___x_2064_, v___x_2069_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2071_){
_start:
{
lean_object* v_parents_2072_; lean_object* v_idxs_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_parents_2072_ = lean_ctor_get(v_t_2071_, 1);
v_idxs_2073_ = lean_ctor_get(v_t_2071_, 2);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_array_get_size(v_parents_2072_);
v___x_2076_ = lean_nat_dec_lt(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
return v_t_2071_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_inc_ref(v_idxs_2073_);
v___x_2077_ = l_Lean_Syntax_Traverser_up(v_t_2071_);
v___x_2078_ = lean_array_get_size(v_idxs_2073_);
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = lean_nat_sub(v___x_2078_, v___x_2079_);
v___x_2081_ = lean_array_get(v___x_2074_, v_idxs_2073_, v___x_2080_);
lean_dec(v___x_2080_);
lean_dec_ref(v_idxs_2073_);
v___x_2082_ = lean_nat_add(v___x_2081_, v___x_2079_);
lean_dec(v___x_2081_);
v___x_2083_ = l_Lean_Syntax_Traverser_down(v___x_2077_, v___x_2082_);
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2084_){
_start:
{
lean_object* v_cur_2085_; 
v_cur_2085_ = lean_ctor_get(v_self_2084_, 0);
lean_inc(v_cur_2085_);
return v_cur_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2086_);
lean_dec_ref(v_self_2086_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2089_, lean_object* v_t_2090_){
_start:
{
lean_object* v_toApplicative_2091_; lean_object* v_toFunctor_2092_; lean_object* v_map_2093_; lean_object* v_get_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; 
v_toApplicative_2091_ = lean_ctor_get(v_inst_2089_, 0);
lean_inc_ref(v_toApplicative_2091_);
lean_dec_ref(v_inst_2089_);
v_toFunctor_2092_ = lean_ctor_get(v_toApplicative_2091_, 0);
lean_inc_ref(v_toFunctor_2092_);
lean_dec_ref(v_toApplicative_2091_);
v_map_2093_ = lean_ctor_get(v_toFunctor_2092_, 0);
lean_inc(v_map_2093_);
lean_dec_ref(v_toFunctor_2092_);
v_get_2094_ = lean_ctor_get(v_t_2090_, 0);
lean_inc(v_get_2094_);
lean_dec_ref(v_t_2090_);
v___f_2095_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2096_ = lean_apply_4(v_map_2093_, lean_box(0), lean_box(0), v___f_2095_, v_get_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2097_, lean_object* v_inst_2098_, lean_object* v_t_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2098_, v_t_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2101_, lean_object* v_s_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Lean_Syntax_Traverser_setCur(v_s_2102_, v_stx_2101_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2106_, lean_object* v_stx_2107_){
_start:
{
lean_object* v_modifyGet_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; 
v_modifyGet_2108_ = lean_ctor_get(v_t_2106_, 2);
lean_inc(v_modifyGet_2108_);
lean_dec_ref(v_t_2106_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2109_, 0, v_stx_2107_);
v___x_2110_ = lean_apply_2(v_modifyGet_2108_, lean_box(0), v___f_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2111_, lean_object* v_t_2112_, lean_object* v_stx_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2112_, v_stx_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2115_, lean_object* v_s_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_box(0);
v___x_2118_ = l_Lean_Syntax_Traverser_down(v_s_2116_, v_idx_2115_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2120_, lean_object* v_idx_2121_){
_start:
{
lean_object* v_modifyGet_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; 
v_modifyGet_2122_ = lean_ctor_get(v_t_2120_, 2);
lean_inc(v_modifyGet_2122_);
lean_dec_ref(v_t_2120_);
v___f_2123_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2123_, 0, v_idx_2121_);
v___x_2124_ = lean_apply_2(v_modifyGet_2122_, lean_box(0), v___f_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2125_, lean_object* v_t_2126_, lean_object* v_idx_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2126_, v_idx_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_box(0);
v___x_2131_ = l_Lean_Syntax_Traverser_up(v_s_2129_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2134_){
_start:
{
lean_object* v_modifyGet_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; 
v_modifyGet_2135_ = lean_ctor_get(v_t_2134_, 2);
lean_inc(v_modifyGet_2135_);
lean_dec_ref(v_t_2134_);
v___f_2136_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2137_ = lean_apply_2(v_modifyGet_2135_, lean_box(0), v___f_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2138_, lean_object* v_t_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2141_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = l_Lean_Syntax_Traverser_left(v_s_2141_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2146_){
_start:
{
lean_object* v_modifyGet_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; 
v_modifyGet_2147_ = lean_ctor_get(v_t_2146_, 2);
lean_inc(v_modifyGet_2147_);
lean_dec_ref(v_t_2146_);
v___f_2148_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2149_ = lean_apply_2(v_modifyGet_2147_, lean_box(0), v___f_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2150_, lean_object* v_t_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Lean_Syntax_Traverser_right(v_s_2153_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2158_){
_start:
{
lean_object* v_modifyGet_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; 
v_modifyGet_2159_ = lean_ctor_get(v_t_2158_, 2);
lean_inc(v_modifyGet_2159_);
lean_dec_ref(v_t_2158_);
v___f_2160_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2161_ = lean_apply_2(v_modifyGet_2159_, lean_box(0), v___f_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2162_, lean_object* v_t_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2165_, lean_object* v_st_2166_){
_start:
{
lean_object* v_idxs_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_idxs_2167_ = lean_ctor_get(v_st_2166_, 2);
v___x_2168_ = lean_array_get_size(v_idxs_2167_);
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_sub(v___x_2168_, v___x_2169_);
v___x_2171_ = lean_nat_dec_lt(v___x_2170_, v___x_2168_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = lean_apply_2(v_toPure_2165_, lean_box(0), v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_array_fget_borrowed(v_idxs_2167_, v___x_2170_);
lean_dec(v___x_2170_);
lean_inc(v___x_2174_);
v___x_2175_ = lean_apply_2(v_toPure_2165_, lean_box(0), v___x_2174_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2176_, lean_object* v_st_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2176_, v_st_2177_);
lean_dec_ref(v_st_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2179_, lean_object* v_t_2180_){
_start:
{
lean_object* v_toApplicative_2181_; lean_object* v_toBind_2182_; lean_object* v_get_2183_; lean_object* v_toPure_2184_; lean_object* v___f_2185_; lean_object* v___x_2186_; 
v_toApplicative_2181_ = lean_ctor_get(v_inst_2179_, 0);
lean_inc_ref(v_toApplicative_2181_);
v_toBind_2182_ = lean_ctor_get(v_inst_2179_, 1);
lean_inc(v_toBind_2182_);
lean_dec_ref(v_inst_2179_);
v_get_2183_ = lean_ctor_get(v_t_2180_, 0);
lean_inc(v_get_2183_);
lean_dec_ref(v_t_2180_);
v_toPure_2184_ = lean_ctor_get(v_toApplicative_2181_, 1);
lean_inc(v_toPure_2184_);
lean_dec_ref(v_toApplicative_2181_);
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2185_, 0, v_toPure_2184_);
v___x_2186_ = lean_apply_4(v_toBind_2182_, lean_box(0), lean_box(0), v_get_2183_, v___f_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2187_, lean_object* v_inst_2188_, lean_object* v_t_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2188_, v_t_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2191_, lean_object* v_i_2192_){
_start:
{
lean_object* v_args_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_args_2193_ = lean_ctor_get(v_n_2191_, 2);
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_array_get_borrowed(v___x_2194_, v_args_2193_, v_i_2192_);
v___x_2196_ = l_Lean_Syntax_getId(v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2197_, lean_object* v_i_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_SyntaxNode_getIdAt(v_n_2197_, v_i_2198_);
lean_dec(v_i_2198_);
lean_dec(v_n_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2200_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2202_ = lean_box(2);
v___x_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2201_);
lean_ctor_set(v___x_2203_, 2, v_args_2200_);
return v___x_2203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2209_){
_start:
{
if (lean_obj_tag(v_x_2209_) == 1)
{
lean_object* v_kind_2210_; 
v_kind_2210_ = lean_ctor_get(v_x_2209_, 1);
if (lean_obj_tag(v_kind_2210_) == 1)
{
lean_object* v_pre_2211_; lean_object* v_str_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_pre_2211_ = lean_ctor_get(v_kind_2210_, 0);
v_str_2212_ = lean_ctor_get(v_kind_2210_, 1);
v___x_2213_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2214_ = lean_string_dec_eq(v_str_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2216_ = lean_string_dec_eq(v_str_2212_, v___x_2215_);
if (v___x_2216_ == 0)
{
return v___x_2216_;
}
else
{
if (lean_obj_tag(v_pre_2211_) == 1)
{
lean_object* v_pre_2217_; 
v_pre_2217_ = lean_ctor_get(v_pre_2211_, 0);
if (lean_obj_tag(v_pre_2217_) == 1)
{
lean_object* v_pre_2218_; 
v_pre_2218_ = lean_ctor_get(v_pre_2217_, 0);
if (lean_obj_tag(v_pre_2218_) == 1)
{
lean_object* v_pre_2219_; 
v_pre_2219_ = lean_ctor_get(v_pre_2218_, 0);
if (lean_obj_tag(v_pre_2219_) == 0)
{
lean_object* v_str_2220_; lean_object* v_str_2221_; lean_object* v_str_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_str_2220_ = lean_ctor_get(v_pre_2211_, 1);
v_str_2221_ = lean_ctor_get(v_pre_2217_, 1);
v_str_2222_ = lean_ctor_get(v_pre_2218_, 1);
v___x_2223_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2224_ = lean_string_dec_eq(v_str_2222_, v___x_2223_);
if (v___x_2224_ == 0)
{
return v___x_2214_;
}
else
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2226_ = lean_string_dec_eq(v_str_2221_, v___x_2225_);
if (v___x_2226_ == 0)
{
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2228_ = lean_string_dec_eq(v_str_2220_, v___x_2227_);
return v___x_2228_;
}
}
}
else
{
return v___x_2214_;
}
}
else
{
return v___x_2214_;
}
}
else
{
return v___x_2214_;
}
}
else
{
return v___x_2214_;
}
}
}
else
{
return v___x_2214_;
}
}
else
{
uint8_t v___x_2229_; 
v___x_2229_ = 0;
return v___x_2229_;
}
}
else
{
uint8_t v___x_2230_; 
v___x_2230_ = 0;
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2231_){
_start:
{
uint8_t v_res_2232_; lean_object* v_r_2233_; 
v_res_2232_ = l_Lean_Syntax_isQuot(v_x_2231_);
lean_dec(v_x_2231_);
v_r_2233_ = lean_box(v_res_2232_);
return v_r_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2239_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___y_2243_; uint8_t v___x_2249_; 
v___x_2240_ = l_Lean_Syntax_getNumArgs(v_stx_2239_);
v___x_2241_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_dec_eq(v___x_2240_, v___x_2241_);
lean_dec(v___x_2240_);
if (v___x_2249_ == 0)
{
v___y_2243_ = v_stx_2239_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = l_Lean_Syntax_getArg(v_stx_2239_, v___x_2250_);
lean_dec(v_stx_2239_);
v___y_2243_ = v___x_2251_;
goto v___jp_2242_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2243_);
v___x_2245_ = l_Lean_Syntax_isOfKind(v___y_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Syntax_getArg(v___y_2243_, v___x_2241_);
lean_dec(v___y_2243_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_unsigned_to_nat(3u);
v___x_2248_ = l_Lean_Syntax_getArg(v___y_2243_, v___x_2247_);
lean_dec(v___y_2243_);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2253_){
_start:
{
if (lean_obj_tag(v_x_2253_) == 1)
{
lean_object* v_kind_2254_; 
v_kind_2254_ = lean_ctor_get(v_x_2253_, 1);
if (lean_obj_tag(v_kind_2254_) == 1)
{
lean_object* v_str_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_str_2255_ = lean_ctor_get(v_kind_2254_, 1);
v___x_2256_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2257_ = lean_string_dec_eq(v_str_2255_, v___x_2256_);
return v___x_2257_;
}
else
{
uint8_t v___x_2258_; 
v___x_2258_ = 0;
return v___x_2258_;
}
}
else
{
uint8_t v___x_2259_; 
v___x_2259_ = 0;
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2260_){
_start:
{
uint8_t v_res_2261_; lean_object* v_r_2262_; 
v_res_2261_ = l_Lean_Syntax_isAntiquot(v_x_2260_);
lean_dec(v_x_2260_);
v_r_2262_ = lean_box(v_res_2261_);
return v_r_2262_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object* v___x_2263_, uint8_t v___x_2264_, lean_object* v_as_2265_, size_t v_i_2266_, size_t v_stop_2267_){
_start:
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_usize_dec_eq(v_i_2266_, v_stop_2267_);
if (v___x_2268_ == 0)
{
uint8_t v___x_2269_; uint8_t v___y_2271_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2269_ = 1;
v___x_2275_ = lean_array_uget_borrowed(v_as_2265_, v_i_2266_);
v___x_2276_ = l_Lean_Syntax_isAntiquot(v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = lean_nat_dec_lt(v___x_2277_, v___x_2263_);
v___y_2271_ = v___x_2278_;
goto v___jp_2270_;
}
else
{
v___y_2271_ = v___x_2264_;
goto v___jp_2270_;
}
v___jp_2270_:
{
if (v___y_2271_ == 0)
{
size_t v___x_2272_; size_t v___x_2273_; 
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2266_, v___x_2272_);
v_i_2266_ = v___x_2273_;
goto _start;
}
else
{
return v___x_2269_;
}
}
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = 0;
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___x_2280_, lean_object* v___x_2281_, lean_object* v_as_2282_, lean_object* v_i_2283_, lean_object* v_stop_2284_){
_start:
{
uint8_t v___x_341__boxed_2285_; size_t v_i_boxed_2286_; size_t v_stop_boxed_2287_; uint8_t v_res_2288_; lean_object* v_r_2289_; 
v___x_341__boxed_2285_ = lean_unbox(v___x_2281_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2283_);
lean_dec(v_i_2283_);
v_stop_boxed_2287_ = lean_unbox_usize(v_stop_2284_);
lean_dec(v_stop_2284_);
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2280_, v___x_341__boxed_2285_, v_as_2282_, v_i_boxed_2286_, v_stop_boxed_2287_);
lean_dec_ref(v_as_2282_);
lean_dec(v___x_2280_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2290_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = l_Lean_Syntax_isAntiquot(v_stx_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2290_);
v___x_2293_ = l_Lean_Syntax_isOfKind(v_stx_2290_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_dec(v_stx_2290_);
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = l_Lean_Syntax_getNumArgs(v_stx_2290_);
v___x_2296_ = lean_nat_dec_lt(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_dec(v___x_2295_);
lean_dec(v_stx_2290_);
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = l_Lean_Syntax_getArgs(v_stx_2290_);
lean_dec(v_stx_2290_);
v___x_2298_ = lean_array_get_size(v___x_2297_);
v___x_2299_ = lean_nat_dec_lt(v___x_2294_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_dec_ref(v___x_2297_);
lean_dec(v___x_2295_);
return v___x_2296_;
}
else
{
if (v___x_2299_ == 0)
{
lean_dec_ref(v___x_2297_);
lean_dec(v___x_2295_);
return v___x_2296_;
}
else
{
size_t v___x_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2298_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2295_, v___x_2291_, v___x_2297_, v___x_2300_, v___x_2301_);
lean_dec_ref(v___x_2297_);
lean_dec(v___x_2295_);
if (v___x_2302_ == 0)
{
return v___x_2299_;
}
else
{
return v___x_2291_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_2290_);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2303_){
_start:
{
uint8_t v_res_2304_; lean_object* v_r_2305_; 
v_res_2304_ = l_Lean_Syntax_isAntiquots(v_stx_2303_);
v_r_2305_ = lean_box(v_res_2304_);
return v_r_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2306_){
_start:
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2306_);
v___x_2308_ = l_Lean_Syntax_isOfKind(v_stx_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
return v_stx_2306_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = l_Lean_Syntax_getArg(v_stx_2306_, v___x_2309_);
lean_dec(v_stx_2306_);
return v___x_2310_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2313_ = l_Lean_mkAtom(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2317_ = lean_unsigned_to_nat(4u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
v___x_2319_ = lean_array_push(v___x_2318_, v___x_2316_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2328_ = l_Lean_mkAtom(v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2330_ = lean_unsigned_to_nat(2u);
v___x_2331_ = lean_mk_empty_array_with_capacity(v___x_2330_);
v___x_2332_ = lean_array_push(v___x_2331_, v___x_2329_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2344_ = l_Lean_mkAtom(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2347_ = l_Lean_mkAtom(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2348_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2349_ = lean_unsigned_to_nat(3u);
v___x_2350_ = lean_mk_empty_array_with_capacity(v___x_2349_);
v___x_2351_ = lean_array_push(v___x_2350_, v___x_2348_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2352_, lean_object* v_term_2353_, lean_object* v_nesting_2354_, lean_object* v_name_2355_, uint8_t v_isPseudoKind_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_nesting_2361_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2380_; uint8_t v___x_2388_; 
v___x_2357_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2358_ = lean_mk_array(v_nesting_2354_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2360_ = lean_box(2);
v_nesting_2361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2361_, 0, v___x_2360_);
lean_ctor_set(v_nesting_2361_, 1, v___x_2359_);
lean_ctor_set(v_nesting_2361_, 2, v___x_2358_);
v___x_2388_ = l_Lean_Syntax_isIdent(v_term_2353_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2353_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v_term_2353_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2391_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2392_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2393_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2394_ = lean_array_push(v___x_2393_, v_term_2353_);
v___x_2395_ = lean_array_push(v___x_2394_, v___x_2392_);
v___x_2396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2360_);
lean_ctor_set(v___x_2396_, 1, v___x_2391_);
lean_ctor_set(v___x_2396_, 2, v___x_2395_);
v___y_2380_ = v___x_2396_;
goto v___jp_2379_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(0u);
v___x_2398_ = l_Lean_Syntax_getArg(v_term_2353_, v___x_2397_);
lean_dec(v_term_2353_);
v___y_2380_ = v___x_2398_;
goto v___jp_2379_;
}
}
else
{
v___y_2380_ = v_term_2353_;
goto v___jp_2379_;
}
v___jp_2362_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_inc(v___y_2365_);
v___x_2366_ = l_Lean_Name_append(v_kind_2352_, v___y_2365_);
v___x_2367_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2368_ = l_Lean_Name_append(v___x_2366_, v___x_2367_);
v___x_2369_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2370_ = lean_array_push(v___x_2369_, v_nesting_2361_);
v___x_2371_ = lean_array_push(v___x_2370_, v___y_2363_);
v___x_2372_ = lean_array_push(v___x_2371_, v___y_2364_);
v___x_2373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2360_);
lean_ctor_set(v___x_2373_, 1, v___x_2368_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
return v___x_2373_;
}
v___jp_2374_:
{
if (v_isPseudoKind_2356_ == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_box(0);
v___y_2363_ = v___y_2375_;
v___y_2364_ = v___y_2376_;
v___y_2365_ = v___x_2377_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2378_; 
v___x_2378_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2363_ = v___y_2375_;
v___y_2364_ = v___y_2376_;
v___y_2365_ = v___x_2378_;
goto v___jp_2362_;
}
}
v___jp_2379_:
{
if (lean_obj_tag(v_name_2355_) == 0)
{
lean_object* v___x_2381_; 
v___x_2381_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2375_ = v___y_2380_;
v___y_2376_ = v___x_2381_;
goto v___jp_2374_;
}
else
{
lean_object* v_val_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_val_2382_ = lean_ctor_get(v_name_2355_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v_name_2355_, 1);
v___x_2383_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2384_ = l_Lean_mkAtom(v_val_2382_);
v___x_2385_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2386_ = lean_array_push(v___x_2385_, v___x_2384_);
v___x_2387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2360_);
lean_ctor_set(v___x_2387_, 1, v___x_2383_);
lean_ctor_set(v___x_2387_, 2, v___x_2386_);
v___y_2375_ = v___y_2380_;
v___y_2376_ = v___x_2387_;
goto v___jp_2374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2399_, lean_object* v_term_2400_, lean_object* v_nesting_2401_, lean_object* v_name_2402_, lean_object* v_isPseudoKind_2403_){
_start:
{
uint8_t v_isPseudoKind_boxed_2404_; lean_object* v_res_2405_; 
v_isPseudoKind_boxed_2404_ = lean_unbox(v_isPseudoKind_2403_);
v_res_2405_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2399_, v_term_2400_, v_nesting_2401_, v_name_2402_, v_isPseudoKind_boxed_2404_);
return v_res_2405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2406_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = l_Lean_Syntax_getArg(v_stx_2406_, v___x_2407_);
v___x_2409_ = l_Lean_Syntax_getArgs(v___x_2408_);
lean_dec(v___x_2408_);
v___x_2410_ = lean_array_get_size(v___x_2409_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = lean_nat_dec_eq(v___x_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
uint8_t v___x_2413_; 
v___x_2413_ = 1;
return v___x_2413_;
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = 0;
return v___x_2414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2415_){
_start:
{
uint8_t v_res_2416_; lean_object* v_r_2417_; 
v_res_2416_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2415_);
lean_dec(v_stx_2415_);
v_r_2417_ = lean_box(v_res_2416_);
return v_r_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = l_Lean_Syntax_isAntiquot(v_stx_2418_);
if (v___x_2419_ == 0)
{
return v_stx_2418_;
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = l_Lean_Syntax_getArg(v_stx_2418_, v___x_2420_);
v___x_2422_ = l_Lean_Syntax_getArgs(v___x_2421_);
lean_dec(v___x_2421_);
v___x_2423_ = lean_array_pop(v___x_2422_);
v___x_2424_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2425_ = lean_box(2);
v___x_2426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_2424_);
lean_ctor_set(v___x_2426_, 2, v___x_2423_);
v___x_2427_ = l_Lean_Syntax_setArg(v_stx_2418_, v___x_2420_, v___x_2426_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2428_){
_start:
{
lean_object* v___y_2430_; uint8_t v___x_2441_; 
v___x_2441_ = l_Lean_Syntax_isAntiquot(v_stx_2428_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_unsigned_to_nat(3u);
v___x_2443_ = l_Lean_Syntax_getArg(v_stx_2428_, v___x_2442_);
v___y_2430_ = v___x_2443_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_unsigned_to_nat(2u);
v___x_2445_ = l_Lean_Syntax_getArg(v_stx_2428_, v___x_2444_);
v___y_2430_ = v___x_2445_;
goto v___jp_2429_;
}
v___jp_2429_:
{
uint8_t v___x_2431_; 
v___x_2431_ = l_Lean_Syntax_isIdent(v___y_2430_);
if (v___x_2431_ == 0)
{
uint8_t v___x_2432_; 
v___x_2432_ = l_Lean_Syntax_isAtom(v___y_2430_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = l_Lean_Syntax_getArg(v___y_2430_, v___x_2433_);
lean_dec(v___y_2430_);
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2435_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2436_ = lean_unsigned_to_nat(1u);
v___x_2437_ = lean_mk_empty_array_with_capacity(v___x_2436_);
v___x_2438_ = lean_array_push(v___x_2437_, v___y_2430_);
v___x_2439_ = lean_box(2);
v___x_2440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___x_2435_);
lean_ctor_set(v___x_2440_, 2, v___x_2438_);
return v___x_2440_;
}
}
else
{
return v___y_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2446_);
lean_dec(v_stx_2446_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2448_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 1)
{
lean_object* v_kind_2449_; 
v_kind_2449_ = lean_ctor_get(v_x_2448_, 1);
if (lean_obj_tag(v_kind_2449_) == 1)
{
lean_object* v_pre_2450_; lean_object* v_str_2451_; 
v_pre_2450_ = lean_ctor_get(v_kind_2449_, 0);
v_str_2451_ = lean_ctor_get(v_kind_2449_, 1);
if (lean_obj_tag(v_pre_2450_) == 1)
{
lean_object* v_pre_2457_; lean_object* v_str_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_pre_2457_ = lean_ctor_get(v_pre_2450_, 0);
v_str_2458_ = lean_ctor_get(v_pre_2450_, 1);
v___x_2459_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2460_ = lean_string_dec_eq(v_str_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2462_ = lean_string_dec_eq(v_str_2451_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_box(0);
return v___x_2463_;
}
else
{
goto v___jp_2452_;
}
}
else
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2465_ = lean_string_dec_eq(v_str_2451_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_box(0);
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_box(v___x_2465_);
lean_inc(v_pre_2457_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_pre_2457_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
}
else
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2471_ = lean_string_dec_eq(v_str_2451_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_box(0);
return v___x_2472_;
}
else
{
goto v___jp_2452_;
}
}
v___jp_2452_:
{
uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2453_ = 0;
v___x_2454_ = lean_box(v___x_2453_);
lean_inc(v_pre_2450_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_pre_2450_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_box(0);
return v___x_2473_;
}
}
else
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_box(0);
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2475_);
lean_dec(v_x_2475_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2477_, size_t v_i_2478_, size_t v_stop_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v___y_2482_; uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_eq(v_i_2478_, v_stop_2479_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_array_uget_borrowed(v_as_2477_, v_i_2478_);
v___x_2488_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2487_);
if (lean_obj_tag(v___x_2488_) == 0)
{
v___y_2482_ = v_b_2480_;
goto v___jp_2481_;
}
else
{
lean_object* v_val_2489_; lean_object* v___x_2490_; 
v_val_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_val_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = lean_array_push(v_b_2480_, v_val_2489_);
v___y_2482_ = v___x_2490_;
goto v___jp_2481_;
}
}
else
{
return v_b_2480_;
}
v___jp_2481_:
{
size_t v___x_2483_; size_t v___x_2484_; 
v___x_2483_ = ((size_t)1ULL);
v___x_2484_ = lean_usize_add(v_i_2478_, v___x_2483_);
v_i_2478_ = v___x_2484_;
v_b_2480_ = v___y_2482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2491_, lean_object* v_i_2492_, lean_object* v_stop_2493_, lean_object* v_b_2494_){
_start:
{
size_t v_i_boxed_2495_; size_t v_stop_boxed_2496_; lean_object* v_res_2497_; 
v_i_boxed_2495_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_stop_boxed_2496_ = lean_unbox_usize(v_stop_2493_);
lean_dec(v_stop_2493_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2491_, v_i_boxed_2495_, v_stop_boxed_2496_, v_b_2494_);
lean_dec_ref(v_as_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2500_, lean_object* v_start_2501_, lean_object* v_stop_2502_){
_start:
{
lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2504_ = lean_nat_dec_lt(v_start_2501_, v_stop_2502_);
if (v___x_2504_ == 0)
{
return v___x_2503_;
}
else
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = lean_array_get_size(v_as_2500_);
v___x_2506_ = lean_nat_dec_le(v_stop_2502_, v___x_2505_);
if (v___x_2506_ == 0)
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_nat_dec_lt(v_start_2501_, v___x_2505_);
if (v___x_2507_ == 0)
{
return v___x_2503_;
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_usize_of_nat(v_start_2501_);
v___x_2509_ = lean_usize_of_nat(v___x_2505_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2500_, v___x_2508_, v___x_2509_, v___x_2503_);
return v___x_2510_;
}
}
else
{
size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_usize_of_nat(v_start_2501_);
v___x_2512_ = lean_usize_of_nat(v_stop_2502_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2500_, v___x_2511_, v___x_2512_, v___x_2503_);
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2514_, lean_object* v_start_2515_, lean_object* v_stop_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2514_, v_start_2515_, v_stop_2516_);
lean_dec(v_stop_2516_);
lean_dec(v_start_2515_);
lean_dec_ref(v_as_2514_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2518_){
_start:
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2518_);
v___x_2520_ = l_Lean_Syntax_isOfKind(v_stx_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2518_);
lean_dec(v_stx_2518_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_box(0);
return v___x_2522_;
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_val_2523_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_val_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
return v___x_2525_;
}
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2526_ = l_Lean_Syntax_getArgs(v_stx_2518_);
lean_dec(v_stx_2518_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_array_get_size(v___x_2526_);
v___x_2529_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2526_, v___x_2527_, v___x_2528_);
lean_dec_ref(v___x_2526_);
v___x_2530_ = lean_array_to_list(v___x_2529_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2532_){
_start:
{
if (lean_obj_tag(v_x_2532_) == 1)
{
lean_object* v_kind_2533_; 
v_kind_2533_ = lean_ctor_get(v_x_2532_, 1);
if (lean_obj_tag(v_kind_2533_) == 1)
{
lean_object* v_pre_2534_; lean_object* v_str_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v_pre_2534_ = lean_ctor_get(v_kind_2533_, 0);
v_str_2535_ = lean_ctor_get(v_kind_2533_, 1);
v___x_2536_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2537_ = lean_string_dec_eq(v_str_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_box(0);
return v___x_2538_;
}
else
{
lean_object* v___x_2539_; 
lean_inc(v_pre_2534_);
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_pre_2534_);
return v___x_2539_;
}
}
else
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_box(0);
return v___x_2540_;
}
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_box(0);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2542_);
lean_dec(v_x_2542_);
return v_res_2543_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
uint8_t v___x_2546_; 
v___x_2546_ = 0;
return v___x_2546_;
}
else
{
uint8_t v___x_2547_; 
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = 1;
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2548_){
_start:
{
uint8_t v_res_2549_; lean_object* v_r_2550_; 
v_res_2549_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2548_);
lean_dec(v_stx_2548_);
v_r_2550_ = lean_box(v_res_2549_);
return v_r_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2551_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_unsigned_to_nat(3u);
v___x_2553_ = l_Lean_Syntax_getArg(v_stx_2551_, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_getArgs(v___x_2553_);
lean_dec(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2555_);
lean_dec(v_stx_2555_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2557_){
_start:
{
uint8_t v___x_2558_; 
v___x_2558_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_unsigned_to_nat(1u);
v___x_2560_ = l_Lean_Syntax_getArg(v_stx_2557_, v___x_2559_);
return v___x_2560_;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_unsigned_to_nat(5u);
v___x_2562_ = l_Lean_Syntax_getArg(v_stx_2557_, v___x_2561_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2563_);
lean_dec(v_stx_2563_);
return v_res_2564_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2570_ = l_Lean_mkAtom(v___x_2569_);
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2573_ = l_Lean_mkAtom(v___x_2572_);
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2574_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2575_ = lean_unsigned_to_nat(6u);
v___x_2576_ = lean_mk_empty_array_with_capacity(v___x_2575_);
v___x_2577_ = lean_array_push(v___x_2576_, v___x_2574_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2578_, lean_object* v_contents_2579_, lean_object* v_suffix_2580_, lean_object* v_nesting_2581_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_nesting_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2582_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2583_ = lean_mk_array(v_nesting_2581_, v___x_2582_);
v___x_2584_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2585_ = lean_box(2);
v_nesting_2586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2586_, 0, v___x_2585_);
lean_ctor_set(v_nesting_2586_, 1, v___x_2584_);
lean_ctor_set(v_nesting_2586_, 2, v___x_2583_);
v___x_2587_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2588_ = l_Lean_Name_append(v_kind_2578_, v___x_2587_);
v___x_2589_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2585_);
lean_ctor_set(v___x_2590_, 1, v___x_2584_);
lean_ctor_set(v___x_2590_, 2, v_contents_2579_);
v___x_2591_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2592_ = l_Lean_mkAtom(v_suffix_2580_);
v___x_2593_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2594_ = lean_array_push(v___x_2593_, v_nesting_2586_);
v___x_2595_ = lean_array_push(v___x_2594_, v___x_2589_);
v___x_2596_ = lean_array_push(v___x_2595_, v___x_2590_);
v___x_2597_ = lean_array_push(v___x_2596_, v___x_2591_);
v___x_2598_ = lean_array_push(v___x_2597_, v___x_2592_);
v___x_2599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2585_);
lean_ctor_set(v___x_2599_, 1, v___x_2588_);
lean_ctor_set(v___x_2599_, 2, v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2601_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 1)
{
lean_object* v_kind_2602_; 
v_kind_2602_ = lean_ctor_get(v_x_2601_, 1);
if (lean_obj_tag(v_kind_2602_) == 1)
{
lean_object* v_pre_2603_; lean_object* v_str_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v_pre_2603_ = lean_ctor_get(v_kind_2602_, 0);
v_str_2604_ = lean_ctor_get(v_kind_2602_, 1);
v___x_2605_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2606_ = lean_string_dec_eq(v_str_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_box(0);
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; 
lean_inc(v_pre_2603_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_pre_2603_);
return v___x_2608_;
}
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_box(0);
return v___x_2609_;
}
}
else
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_box(0);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2611_);
lean_dec(v_x_2611_);
return v_res_2612_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
uint8_t v___x_2615_; 
v___x_2615_ = 0;
return v___x_2615_;
}
else
{
uint8_t v___x_2616_; 
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = 1;
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2617_){
_start:
{
uint8_t v_res_2618_; lean_object* v_r_2619_; 
v_res_2618_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2617_);
lean_dec(v_stx_2617_);
v_r_2619_ = lean_box(v_res_2618_);
return v_r_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2620_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = l_Lean_Syntax_getArg(v_stx_2620_, v___x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2623_);
lean_dec(v_stx_2623_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2627_, lean_object* v_inner_2628_, lean_object* v_suffix_2629_){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2630_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2631_ = l_Lean_Name_append(v_kind_2627_, v___x_2630_);
v___x_2632_ = l_Lean_mkAtom(v_suffix_2629_);
v___x_2633_ = lean_unsigned_to_nat(2u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v___x_2635_ = lean_array_push(v___x_2634_, v_inner_2628_);
v___x_2636_ = lean_array_push(v___x_2635_, v___x_2632_);
v___x_2637_ = lean_box(2);
v___x_2638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2631_);
lean_ctor_set(v___x_2638_, 2, v___x_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2642_){
_start:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2644_ = l_Lean_Syntax_isOfKind(v_stx_2642_, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2645_){
_start:
{
uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_res_2646_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2645_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2648_){
_start:
{
uint8_t v___x_2649_; 
v___x_2649_ = l_Lean_Syntax_isAntiquot(v_stx_2648_);
if (v___x_2649_ == 0)
{
uint8_t v___x_2650_; 
v___x_2650_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2648_);
if (v___x_2650_ == 0)
{
uint8_t v___x_2651_; 
v___x_2651_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2648_);
if (v___x_2651_ == 0)
{
uint8_t v___x_2652_; 
v___x_2652_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2648_);
return v___x_2652_;
}
else
{
lean_dec(v_stx_2648_);
return v___x_2651_;
}
}
else
{
lean_dec(v_stx_2648_);
return v___x_2650_;
}
}
else
{
lean_dec(v_stx_2648_);
return v___x_2649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2653_){
_start:
{
uint8_t v_res_2654_; lean_object* v_r_2655_; 
v_res_2654_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2653_);
v_r_2655_ = lean_box(v_res_2654_);
return v_r_2655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2659_, lean_object* v_stx_2660_, lean_object* v_visit_2661_, lean_object* v_stack_2662_, lean_object* v_accept_2663_, lean_object* v_a_2664_, lean_object* v_b_2665_){
_start:
{
lean_object* v_a_2667_; uint8_t v___x_2671_; 
v___x_2671_ = lean_nat_dec_lt(v_a_2664_, v_upperBound_2659_);
if (v___x_2671_ == 0)
{
lean_dec(v_a_2664_);
lean_dec_ref(v_accept_2663_);
lean_dec(v_stack_2662_);
lean_dec_ref(v_visit_2661_);
lean_dec(v_stx_2660_);
lean_inc_ref(v_b_2665_);
return v_b_2665_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2674_ = l_Lean_Syntax_getArg(v_stx_2660_, v_a_2664_);
lean_inc_ref(v_visit_2661_);
lean_inc(v___x_2674_);
v___x_2675_ = lean_apply_1(v_visit_2661_, v___x_2674_);
v___x_2676_ = lean_unbox(v___x_2675_);
if (v___x_2676_ == 0)
{
lean_dec(v___x_2674_);
v_a_2667_ = v___x_2673_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_inc(v_a_2664_);
lean_inc(v_stx_2660_);
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v_stx_2660_);
lean_ctor_set(v___x_2677_, 1, v_a_2664_);
lean_inc(v_stack_2662_);
v___x_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v_stack_2662_);
lean_inc_ref(v_accept_2663_);
lean_inc_ref(v_visit_2661_);
v___x_2679_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2661_, v_accept_2663_, v___x_2678_, v___x_2674_);
if (lean_obj_tag(v___x_2679_) == 1)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec(v_a_2664_);
lean_dec_ref(v_accept_2663_);
lean_dec(v_stack_2662_);
lean_dec_ref(v_visit_2661_);
lean_dec(v_stx_2660_);
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___x_2672_);
return v___x_2681_;
}
else
{
lean_dec(v___x_2679_);
v_a_2667_ = v___x_2673_;
goto v___jp_2666_;
}
}
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_add(v_a_2664_, v___x_2668_);
lean_dec(v_a_2664_);
v_a_2664_ = v___x_2669_;
v_b_2665_ = v_a_2667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2682_, lean_object* v_accept_2683_, lean_object* v_stack_2684_, lean_object* v_stx_2685_){
_start:
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
lean_inc_ref(v_accept_2683_);
lean_inc(v_stx_2685_);
v___x_2686_ = lean_apply_1(v_accept_2683_, v_stx_2685_);
v___x_2687_ = lean_unbox(v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v_fst_2693_; 
v___x_2688_ = l_Lean_Syntax_getNumArgs(v_stx_2685_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_box(0);
v___x_2691_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2688_, v_stx_2685_, v_visit_2682_, v_stack_2684_, v_accept_2683_, v___x_2689_, v___x_2691_);
lean_dec(v___x_2688_);
v_fst_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_fst_2693_);
lean_dec_ref(v___x_2692_);
if (lean_obj_tag(v_fst_2693_) == 0)
{
return v___x_2690_;
}
else
{
lean_object* v_val_2694_; 
v_val_2694_ = lean_ctor_get(v_fst_2693_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v_fst_2693_, 1);
return v_val_2694_;
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_accept_2683_);
lean_dec_ref(v_visit_2682_);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_stx_2685_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v_stack_2684_);
v___x_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2699_, lean_object* v_stx_2700_, lean_object* v_visit_2701_, lean_object* v_stack_2702_, lean_object* v_accept_2703_, lean_object* v_a_2704_, lean_object* v_b_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2699_, v_stx_2700_, v_visit_2701_, v_stack_2702_, v_accept_2703_, v_a_2704_, v_b_2705_);
lean_dec_ref(v_b_2705_);
lean_dec(v_upperBound_2699_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2707_, lean_object* v_stx_2708_, lean_object* v_visit_2709_, lean_object* v_stack_2710_, lean_object* v_accept_2711_, lean_object* v_inst_2712_, lean_object* v_R_2713_, lean_object* v_a_2714_, lean_object* v_b_2715_, lean_object* v_c_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2707_, v_stx_2708_, v_visit_2709_, v_stack_2710_, v_accept_2711_, v_a_2714_, v_b_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2718_, lean_object* v_stx_2719_, lean_object* v_visit_2720_, lean_object* v_stack_2721_, lean_object* v_accept_2722_, lean_object* v_inst_2723_, lean_object* v_R_2724_, lean_object* v_a_2725_, lean_object* v_b_2726_, lean_object* v_c_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2718_, v_stx_2719_, v_visit_2720_, v_stack_2721_, v_accept_2722_, v_inst_2723_, v_R_2724_, v_a_2725_, v_b_2726_, v_c_2727_);
lean_dec_ref(v_b_2726_);
lean_dec(v_upperBound_2718_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2729_, lean_object* v_visit_2730_, lean_object* v_accept_2731_){
_start:
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
lean_inc_ref(v_visit_2730_);
lean_inc(v_root_2729_);
v___x_2732_ = lean_apply_1(v_visit_2730_, v_root_2729_);
v___x_2733_ = lean_unbox(v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; 
lean_dec_ref(v_accept_2731_);
lean_dec_ref(v_visit_2730_);
lean_dec(v_root_2729_);
v___x_2734_ = lean_box(0);
return v___x_2734_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2730_, v_accept_2731_, v___x_2735_, v_root_2729_);
return v___x_2736_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2737_, lean_object* v_x_2738_, lean_object* v_p_2739_){
_start:
{
if (lean_obj_tag(v_p_2739_) == 0)
{
lean_dec_ref(v_x_2738_);
return v___x_2737_;
}
else
{
lean_object* v_fst_2740_; lean_object* v_val_2741_; uint8_t v___x_2742_; 
v_fst_2740_ = lean_ctor_get(v_x_2738_, 0);
lean_inc(v_fst_2740_);
lean_dec_ref(v_x_2738_);
v_val_2741_ = lean_ctor_get(v_p_2739_, 0);
v___x_2742_ = l_Lean_Syntax_isOfKind(v_fst_2740_, v_val_2741_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v_p_2745_){
_start:
{
uint8_t v___x_123__boxed_2746_; uint8_t v_res_2747_; lean_object* v_r_2748_; 
v___x_123__boxed_2746_ = lean_unbox(v___x_2743_);
v_res_2747_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2746_, v_x_2744_, v_p_2745_);
lean_dec(v_p_2745_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2749_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
uint8_t v___x_2750_; 
v___x_2750_ = 1;
return v___x_2750_;
}
else
{
lean_object* v_head_2751_; uint8_t v___x_2752_; 
v_head_2751_ = lean_ctor_get(v_x_2749_, 0);
v___x_2752_ = lean_unbox(v_head_2751_);
if (v___x_2752_ == 0)
{
uint8_t v___x_2753_; 
v___x_2753_ = lean_unbox(v_head_2751_);
return v___x_2753_;
}
else
{
lean_object* v_tail_2754_; 
v_tail_2754_ = lean_ctor_get(v_x_2749_, 1);
v_x_2749_ = v_tail_2754_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2756_){
_start:
{
uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_res_2757_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2756_);
lean_dec(v_x_2756_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2761_, lean_object* v_pattern_2762_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2763_ = l_List_lengthTR___redArg(v_pattern_2762_);
v___x_2764_ = l_List_lengthTR___redArg(v_stack_2761_);
v___x_2765_ = lean_nat_dec_le(v___x_2763_, v___x_2764_);
lean_dec(v___x_2764_);
lean_dec(v___x_2763_);
if (v___x_2765_ == 0)
{
lean_dec(v_pattern_2762_);
lean_dec(v_stack_2761_);
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; lean_object* v___f_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2766_ = lean_box(v___x_2765_);
v___f_2767_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2767_, 0, v___x_2766_);
v___x_2768_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2769_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2767_, v_stack_2761_, v_pattern_2762_, v___x_2768_);
v___x_2770_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2769_);
lean_dec(v___x_2769_);
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2771_, lean_object* v_pattern_2772_){
_start:
{
uint8_t v_res_2773_; lean_object* v_r_2774_; 
v_res_2773_ = l_Lean_Syntax_Stack_matches(v_stack_2771_, v_pattern_2772_);
v_r_2774_ = lean_box(v_res_2773_);
return v_r_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2775_, lean_object* v_trailing_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2775_);
if (lean_obj_tag(v___x_2777_) == 1)
{
lean_object* v_val_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2813_; 
v_val_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2813_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_val_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2813_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
if (lean_obj_tag(v_val_2778_) == 0)
{
lean_object* v_trailing_2782_; lean_object* v_leading_2783_; lean_object* v_pos_2784_; lean_object* v_endPos_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2811_; 
v_trailing_2782_ = lean_ctor_get(v_val_2778_, 2);
v_leading_2783_ = lean_ctor_get(v_val_2778_, 0);
v_pos_2784_ = lean_ctor_get(v_val_2778_, 1);
v_endPos_2785_ = lean_ctor_get(v_val_2778_, 3);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_val_2778_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2787_ = v_val_2778_;
v_isShared_2788_ = v_isSharedCheck_2811_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_endPos_2785_);
lean_inc(v_trailing_2782_);
lean_inc(v_pos_2784_);
lean_inc(v_leading_2783_);
lean_dec(v_val_2778_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2811_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_str_2789_; lean_object* v_startPos_2790_; lean_object* v_stopPos_2791_; lean_object* v_startPos_2792_; lean_object* v_stopPos_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2809_; 
v_str_2789_ = lean_ctor_get(v_trailing_2782_, 0);
lean_inc_ref(v_str_2789_);
v_startPos_2790_ = lean_ctor_get(v_trailing_2782_, 1);
lean_inc(v_startPos_2790_);
v_stopPos_2791_ = lean_ctor_get(v_trailing_2782_, 2);
lean_inc(v_stopPos_2791_);
lean_dec_ref(v_trailing_2782_);
v_startPos_2792_ = lean_ctor_get(v_trailing_2776_, 1);
v_stopPos_2793_ = lean_ctor_get(v_trailing_2776_, 2);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_trailing_2776_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v_trailing_2776_, 0);
lean_dec(v_unused_2810_);
v___x_2795_ = v_trailing_2776_;
v_isShared_2796_ = v_isSharedCheck_2809_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_stopPos_2793_);
lean_inc(v_startPos_2792_);
lean_dec(v_trailing_2776_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2809_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
uint8_t v_decide_2797_; 
v_decide_2797_ = lean_nat_dec_eq(v_stopPos_2791_, v_startPos_2792_);
lean_dec(v_startPos_2792_);
lean_dec(v_stopPos_2791_);
if (v_decide_2797_ == 0)
{
lean_object* v___x_2798_; 
lean_del_object(v___x_2795_);
lean_dec(v_stopPos_2793_);
lean_dec(v_startPos_2790_);
lean_dec_ref(v_str_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_endPos_2785_);
lean_dec(v_pos_2784_);
lean_dec_ref(v_leading_2783_);
lean_del_object(v___x_2780_);
lean_dec(v_stx_2775_);
v___x_2798_ = lean_box(0);
return v___x_2798_;
}
else
{
lean_object* v_trailing_2800_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v_startPos_2790_);
lean_ctor_set(v___x_2795_, 0, v_str_2789_);
v_trailing_2800_ = v___x_2795_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_str_2789_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_startPos_2790_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_stopPos_2793_);
v_trailing_2800_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2802_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 2, v_trailing_2800_);
v___x_2802_ = v___x_2787_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_leading_2783_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_pos_2784_);
lean_ctor_set(v_reuseFailAlloc_2807_, 2, v_trailing_2800_);
lean_ctor_set(v_reuseFailAlloc_2807_, 3, v_endPos_2785_);
v___x_2802_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2803_ = l_Lean_Syntax_setTailInfo(v_stx_2775_, v___x_2802_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2803_);
v___x_2805_ = v___x_2780_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2812_; 
lean_del_object(v___x_2780_);
lean_dec(v_val_2778_);
lean_dec_ref(v_trailing_2776_);
lean_dec(v_stx_2775_);
v___x_2812_ = lean_box(0);
return v___x_2812_;
}
}
}
else
{
lean_object* v___x_2814_; 
lean_dec(v___x_2777_);
lean_dec_ref(v_trailing_2776_);
lean_dec(v_stx_2775_);
v___x_2814_ = lean_box(0);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2815_, lean_object* v_trailing_2816_){
_start:
{
lean_object* v___x_2817_; 
lean_inc(v_stx_2815_);
v___x_2817_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2815_, v_trailing_2816_);
if (lean_obj_tag(v___x_2817_) == 0)
{
return v_stx_2815_;
}
else
{
lean_object* v_val_2818_; 
lean_dec(v_stx_2815_);
v_val_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_val_2818_);
lean_dec_ref_known(v___x_2817_, 1);
return v_val_2818_;
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

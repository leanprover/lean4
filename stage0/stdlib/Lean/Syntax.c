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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_409_, lean_object* v_x_410_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_417_, v_x_418_);
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
v___x_455_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_453_, v___x_454_);
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
v___x_465_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_463_, v___x_464_);
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
v___x_483_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_481_, v___x_482_);
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
lean_object* v_str_993_; lean_object* v_startPos_994_; lean_object* v_stopPos_995_; uint8_t v___y_997_; uint8_t v___x_1007_; 
v_str_993_ = lean_ctor_get(v_trail_992_, 0);
v_startPos_994_ = lean_ctor_get(v_trail_992_, 1);
v_stopPos_995_ = lean_ctor_get(v_trail_992_, 2);
v___x_1007_ = lean_string_is_valid_pos(v_str_993_, v_startPos_994_);
if (v___x_1007_ == 0)
{
v___y_997_ = v___x_1007_;
goto v___jp_996_;
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_string_is_valid_pos(v_str_993_, v_stopPos_995_);
if (v___x_1008_ == 0)
{
v___y_997_ = v___x_1008_;
goto v___jp_996_;
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_le(v_startPos_994_, v_stopPos_995_);
v___y_997_ = v___x_1009_;
goto v___jp_996_;
}
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object* v_trail_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trail_1010_);
lean_dec_ref(v_trail_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_inst_1016_, lean_object* v_R_1017_, lean_object* v_a_1018_, lean_object* v_b_1019_, lean_object* v_c_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1012_, v___x_1013_, v___x_1015_, v_a_1018_, v_b_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v_inst_1026_, lean_object* v_R_1027_, lean_object* v_a_1028_, lean_object* v_b_1029_, lean_object* v_c_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1022_, v___x_1023_, v___x_1024_, v___x_1025_, v_inst_1026_, v_R_1027_, v_a_1028_, v_b_1029_, v_c_1030_);
lean_dec(v_b_1029_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___x_1024_);
lean_dec(v___x_1023_);
lean_dec(v___x_1022_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___y_1035_; 
switch(lean_obj_tag(v_x_1032_))
{
case 2:
{
lean_object* v_info_1038_; 
v_info_1038_ = lean_ctor_get(v_x_1032_, 0);
lean_inc(v_info_1038_);
if (lean_obj_tag(v_info_1038_) == 0)
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1051_; 
v_val_1039_ = lean_ctor_get(v_x_1032_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_x_1032_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_x_1032_, 0);
lean_dec(v_unused_1052_);
v___x_1041_ = v_x_1032_;
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_x_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_trailing_1043_; lean_object* v_trailStop_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v_trailing_1043_ = lean_ctor_get(v_info_1038_, 2);
v_trailStop_1044_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1043_);
lean_inc(v_trailStop_1044_);
v___x_1045_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1038_, v_a_1033_, v_trailStop_1044_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1045_);
v___x_1047_ = v___x_1041_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_val_1039_);
v___x_1047_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_trailStop_1044_);
return v___x_1049_;
}
}
}
else
{
lean_dec(v_info_1038_);
lean_dec_ref_known(v_x_1032_, 2);
v___y_1035_ = v_a_1033_;
goto v___jp_1034_;
}
}
case 3:
{
lean_object* v_info_1053_; 
v_info_1053_ = lean_ctor_get(v_x_1032_, 0);
lean_inc(v_info_1053_);
if (lean_obj_tag(v_info_1053_) == 0)
{
lean_object* v_rawVal_1054_; lean_object* v_val_1055_; lean_object* v_preresolved_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1068_; 
v_rawVal_1054_ = lean_ctor_get(v_x_1032_, 1);
v_val_1055_ = lean_ctor_get(v_x_1032_, 2);
v_preresolved_1056_ = lean_ctor_get(v_x_1032_, 3);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1032_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_x_1032_, 0);
lean_dec(v_unused_1069_);
v___x_1058_ = v_x_1032_;
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_preresolved_1056_);
lean_inc(v_val_1055_);
lean_inc(v_rawVal_1054_);
lean_dec(v_x_1032_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_trailing_1060_; lean_object* v_trailStop_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v_trailing_1060_ = lean_ctor_get(v_info_1053_, 2);
v_trailStop_1061_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1060_);
lean_inc(v_trailStop_1061_);
v___x_1062_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1053_, v_a_1033_, v_trailStop_1061_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1062_);
v___x_1064_ = v___x_1058_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_rawVal_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_val_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_preresolved_1056_);
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
lean_dec(v_info_1053_);
lean_dec_ref_known(v_x_1032_, 4);
v___y_1035_ = v_a_1033_;
goto v___jp_1034_;
}
}
default: 
{
lean_dec(v_x_1032_);
v___y_1035_ = v_a_1033_;
goto v___jp_1034_;
}
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___y_1035_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
switch(lean_obj_tag(v___y_1070_))
{
case 2:
{
lean_object* v_info_1075_; 
v_info_1075_ = lean_ctor_get(v___y_1070_, 0);
lean_inc(v_info_1075_);
if (lean_obj_tag(v_info_1075_) == 0)
{
lean_object* v_val_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1088_; 
v_val_1076_ = lean_ctor_get(v___y_1070_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___y_1070_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v___y_1070_, 0);
lean_dec(v_unused_1089_);
v___x_1078_ = v___y_1070_;
v_isShared_1079_ = v_isSharedCheck_1088_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_val_1076_);
lean_dec(v___y_1070_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1088_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_trailing_1080_; lean_object* v_trailStop_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v_trailing_1080_ = lean_ctor_get(v_info_1075_, 2);
v_trailStop_1081_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1080_);
lean_inc(v_trailStop_1081_);
v___x_1082_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1075_, v___y_1071_, v_trailStop_1081_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1082_);
v___x_1084_ = v___x_1078_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_val_1076_);
v___x_1084_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_trailStop_1081_);
return v___x_1086_;
}
}
}
else
{
lean_dec(v_info_1075_);
lean_dec_ref_known(v___y_1070_, 2);
goto v___jp_1072_;
}
}
case 3:
{
lean_object* v_info_1090_; 
v_info_1090_ = lean_ctor_get(v___y_1070_, 0);
lean_inc(v_info_1090_);
if (lean_obj_tag(v_info_1090_) == 0)
{
lean_object* v_rawVal_1091_; lean_object* v_val_1092_; lean_object* v_preresolved_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1105_; 
v_rawVal_1091_ = lean_ctor_get(v___y_1070_, 1);
v_val_1092_ = lean_ctor_get(v___y_1070_, 2);
v_preresolved_1093_ = lean_ctor_get(v___y_1070_, 3);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___y_1070_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v___y_1070_, 0);
lean_dec(v_unused_1106_);
v___x_1095_ = v___y_1070_;
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_preresolved_1093_);
lean_inc(v_val_1092_);
lean_inc(v_rawVal_1091_);
lean_dec(v___y_1070_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_trailing_1097_; lean_object* v_trailStop_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v_trailing_1097_ = lean_ctor_get(v_info_1090_, 2);
v_trailStop_1098_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1097_);
lean_inc(v_trailStop_1098_);
v___x_1099_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1090_, v___y_1071_, v_trailStop_1098_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1099_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_rawVal_1091_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_val_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_preresolved_1093_);
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
lean_dec(v_info_1090_);
lean_dec_ref_known(v___y_1070_, 4);
goto v___jp_1072_;
}
}
default: 
{
lean_dec(v___y_1070_);
goto v___jp_1072_;
}
}
v___jp_1072_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___y_1071_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1107_, lean_object* v___y_1108_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 1)
{
lean_object* v_info_1109_; lean_object* v_kind_1110_; lean_object* v_args_1111_; lean_object* v___x_1112_; lean_object* v_fst_1113_; 
v_info_1109_ = lean_ctor_get(v_x_1107_, 0);
lean_inc(v_info_1109_);
v_kind_1110_ = lean_ctor_get(v_x_1107_, 1);
lean_inc(v_kind_1110_);
v_args_1111_ = lean_ctor_get(v_x_1107_, 2);
lean_inc_ref(v_args_1111_);
v___x_1112_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1107_, v___y_1108_);
v_fst_1113_ = lean_ctor_get(v___x_1112_, 0);
if (lean_obj_tag(v_fst_1113_) == 0)
{
lean_object* v_snd_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_snd_1114_ = lean_ctor_get(v___x_1112_, 1);
lean_inc(v_snd_1114_);
lean_dec_ref(v___x_1112_);
v_sz_1115_ = lean_array_size(v_args_1111_);
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1115_, v___x_1116_, v_args_1111_, v_snd_1114_);
v_fst_1118_ = lean_ctor_get(v___x_1117_, 0);
v_snd_1119_ = lean_ctor_get(v___x_1117_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snd_1119_);
lean_inc(v_fst_1118_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1123_, 0, v_info_1109_);
lean_ctor_set(v___x_1123_, 1, v_kind_1110_);
lean_ctor_set(v___x_1123_, 2, v_fst_1118_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_snd_1119_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
lean_inc_ref(v_fst_1113_);
lean_dec_ref(v_args_1111_);
lean_dec(v_kind_1110_);
lean_dec(v_info_1109_);
v_snd_1128_ = lean_ctor_get(v___x_1112_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1112_, 0);
lean_dec(v_unused_1137_);
v___x_1130_ = v___x_1112_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_dec(v___x_1112_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_val_1132_; lean_object* v___x_1134_; 
v_val_1132_ = lean_ctor_get(v_fst_1113_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v_fst_1113_, 1);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_val_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_val_1132_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_snd_1128_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v_fst_1139_; 
lean_inc(v_x_1107_);
v___x_1138_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1107_, v___y_1108_);
v_fst_1139_ = lean_ctor_get(v___x_1138_, 0);
if (lean_obj_tag(v_fst_1139_) == 0)
{
lean_object* v_snd_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_snd_1140_ = lean_ctor_get(v___x_1138_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1148_);
v___x_1142_ = v___x_1138_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snd_1140_);
lean_dec(v___x_1138_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_x_1107_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_x_1107_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_snd_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_snd_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
lean_inc_ref(v_fst_1139_);
lean_dec(v_x_1107_);
v_snd_1149_ = lean_ctor_get(v___x_1138_, 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1158_);
v___x_1151_ = v___x_1138_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snd_1149_);
lean_dec(v___x_1138_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_val_1153_; lean_object* v___x_1155_; 
v_val_1153_ = lean_ctor_get(v_fst_1139_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v_fst_1139_, 1);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_val_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_val_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_snd_1149_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1159_, size_t v_i_1160_, lean_object* v_bs_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1160_, v_sz_1159_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_bs_1161_);
lean_ctor_set(v___x_1164_, 1, v___y_1162_);
return v___x_1164_;
}
else
{
lean_object* v_v_1165_; lean_object* v___x_1166_; lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1169_; lean_object* v_bs_x27_1170_; size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
v_v_1165_ = lean_array_uget_borrowed(v_bs_1161_, v_i_1160_);
lean_inc(v_v_1165_);
v___x_1166_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1165_, v___y_1162_);
v_fst_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_fst_1167_);
v_snd_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_snd_1168_);
lean_dec_ref(v___x_1166_);
v___x_1169_ = lean_unsigned_to_nat(0u);
v_bs_x27_1170_ = lean_array_uset(v_bs_1161_, v_i_1160_, v___x_1169_);
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_add(v_i_1160_, v___x_1171_);
v___x_1173_ = lean_array_uset(v_bs_x27_1170_, v_i_1160_, v_fst_1167_);
v_i_1160_ = v___x_1172_;
v_bs_1161_ = v___x_1173_;
v___y_1162_ = v_snd_1168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1175_, lean_object* v_i_1176_, lean_object* v_bs_1177_, lean_object* v___y_1178_){
_start:
{
size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; lean_object* v_res_1181_; 
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1175_);
lean_dec(v_sz_1175_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1179_, v_i_boxed_1180_, v_bs_1177_, v___y_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_fst_1185_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1182_, v___x_1183_);
v_fst_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_fst_1185_);
lean_dec_ref(v___x_1184_);
return v_fst_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1186_, lean_object* v_x_1187_){
_start:
{
switch(lean_obj_tag(v_x_1187_))
{
case 2:
{
lean_object* v_info_1188_; lean_object* v_val_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1197_; 
v_info_1188_ = lean_ctor_get(v_x_1187_, 0);
v_val_1189_ = lean_ctor_get(v_x_1187_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1191_ = v_x_1187_;
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_val_1189_);
lean_inc(v_info_1188_);
lean_dec(v_x_1187_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1186_, v_info_1188_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1193_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_val_1189_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
case 3:
{
lean_object* v_info_1198_; lean_object* v_rawVal_1199_; lean_object* v_val_1200_; lean_object* v_preresolved_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1209_; 
v_info_1198_ = lean_ctor_get(v_x_1187_, 0);
v_rawVal_1199_ = lean_ctor_get(v_x_1187_, 1);
v_val_1200_ = lean_ctor_get(v_x_1187_, 2);
v_preresolved_1201_ = lean_ctor_get(v_x_1187_, 3);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1203_ = v_x_1187_;
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_preresolved_1201_);
lean_inc(v_val_1200_);
lean_inc(v_rawVal_1199_);
lean_inc(v_info_1198_);
lean_dec(v_x_1187_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1186_, v_info_1198_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_rawVal_1199_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_val_1200_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_preresolved_1201_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
case 1:
{
lean_object* v_info_1210_; lean_object* v_kind_1211_; lean_object* v_args_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v_info_1210_ = lean_ctor_get(v_x_1187_, 0);
v_kind_1211_ = lean_ctor_get(v_x_1187_, 1);
v_args_1212_ = lean_ctor_get(v_x_1187_, 2);
v___x_1213_ = lean_array_get_size(v_args_1212_);
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_nat_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1227_; 
lean_inc_ref(v_args_1212_);
lean_inc(v_kind_1211_);
lean_inc(v_info_1210_);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; lean_object* v_unused_1229_; lean_object* v_unused_1230_; 
v_unused_1228_ = lean_ctor_get(v_x_1187_, 2);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_x_1187_, 1);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_x_1187_, 0);
lean_dec(v_unused_1230_);
v___x_1217_ = v_x_1187_;
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v_x_1187_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v_i_1220_; lean_object* v___x_1221_; lean_object* v_last_1222_; lean_object* v_args_1223_; lean_object* v___x_1225_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v_i_1220_ = lean_nat_sub(v___x_1213_, v___x_1219_);
v___x_1221_ = lean_array_fget_borrowed(v_args_1212_, v_i_1220_);
lean_inc(v___x_1221_);
v_last_1222_ = l_Lean_Syntax_updateTrailing(v_trailing_1186_, v___x_1221_);
v_args_1223_ = lean_array_fset(v_args_1212_, v_i_1220_, v_last_1222_);
lean_dec(v_i_1220_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 2, v_args_1223_);
v___x_1225_ = v___x_1217_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_info_1210_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_kind_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_args_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_dec_ref(v_trailing_1186_);
return v_x_1187_;
}
}
default: 
{
lean_dec_ref(v_trailing_1186_);
return v_x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
return v_x_1231_;
}
else
{
lean_object* v_head_1233_; lean_object* v_tail_1234_; lean_object* v___x_1235_; 
v_head_1233_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_head_1233_);
v_tail_1234_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_tail_1234_);
lean_dec_ref_known(v_x_1232_, 2);
v___x_1235_ = l_Lean_Name_append(v_x_1231_, v_head_1233_);
v_x_1231_ = v___x_1235_;
v_x_1232_ = v_tail_1234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1239_, lean_object* v_nFields_x3f_1240_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1240_) == 1)
{
lean_object* v_val_1241_; lean_object* v_nameComps_1242_; lean_object* v___x_1243_; lean_object* v_nPrefix_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_namePrefix_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_val_1241_ = lean_ctor_get(v_nFields_x3f_1240_, 0);
v_nameComps_1242_ = l_Lean_Name_components(v_n_1239_);
v___x_1243_ = l_List_lengthTR___redArg(v_nameComps_1242_);
v_nPrefix_1244_ = lean_nat_sub(v___x_1243_, v_val_1241_);
lean_dec(v___x_1243_);
v___x_1245_ = lean_box(0);
v___x_1246_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1244_);
lean_inc(v_nameComps_1242_);
v___x_1247_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1242_, v_nameComps_1242_, v_nPrefix_1244_, v___x_1246_);
v_namePrefix_1248_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1245_, v___x_1247_);
v___x_1249_ = l_List_drop___redArg(v_nPrefix_1244_, v_nameComps_1242_);
lean_dec(v_nameComps_1242_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_namePrefix_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Name_components(v_n_1239_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1252_, lean_object* v_nFields_x3f_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1252_, v_nFields_x3f_1253_);
lean_dec(v_nFields_x3f_1253_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_panic_fn_borrowed(v___x_1256_, v_msg_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
if (lean_obj_tag(v_x_1259_) == 0)
{
return v_x_1258_;
}
else
{
lean_object* v_head_1260_; lean_object* v_tail_1261_; lean_object* v_startPos_1262_; lean_object* v_stopPos_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_head_1260_ = lean_ctor_get(v_x_1259_, 0);
v_tail_1261_ = lean_ctor_get(v_x_1259_, 1);
v_startPos_1262_ = lean_ctor_get(v_head_1260_, 1);
v_stopPos_1263_ = lean_ctor_get(v_head_1260_, 2);
v___x_1264_ = lean_nat_sub(v_stopPos_1263_, v_startPos_1262_);
v___x_1265_ = lean_nat_add(v_x_1258_, v___x_1264_);
lean_dec(v___x_1264_);
lean_dec(v_x_1258_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v___x_1265_, v___x_1266_);
lean_dec(v___x_1265_);
v_x_1258_ = v___x_1267_;
v_x_1259_ = v_tail_1261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1269_, v_x_1270_);
lean_dec(v_x_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1276_, lean_object* v_pos_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
if (lean_obj_tag(v_a_1278_) == 0)
{
lean_object* v___x_1280_; 
v___x_1280_ = l_List_reverse___redArg(v_a_1279_);
return v___x_1280_;
}
else
{
lean_object* v_head_1281_; lean_object* v_tail_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1300_; 
v_head_1281_ = lean_ctor_get(v_a_1278_, 0);
v_tail_1282_ = lean_ctor_get(v_a_1278_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_a_1278_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1284_ = v_a_1278_;
v_isShared_1285_ = v_isSharedCheck_1300_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_tail_1282_);
lean_inc(v_head_1281_);
lean_dec(v_a_1278_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1300_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_stopPos_1286_; lean_object* v_startPos_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_info_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v_stopPos_1286_ = lean_ctor_get(v_head_1281_, 2);
lean_inc(v_stopPos_1286_);
lean_dec(v_head_1281_);
v_startPos_1287_ = lean_ctor_get(v_rawVal_1276_, 1);
v___x_1288_ = lean_nat_sub(v_stopPos_1286_, v_startPos_1287_);
lean_dec(v_stopPos_1286_);
v___x_1289_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1290_ = lean_nat_add(v___x_1288_, v_pos_1277_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_add(v___x_1291_, v___x_1290_);
v_info_1293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1293_, 0, v___x_1289_);
lean_ctor_set(v_info_1293_, 1, v___x_1290_);
lean_ctor_set(v_info_1293_, 2, v___x_1289_);
lean_ctor_set(v_info_1293_, 3, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_info_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v_a_1279_);
lean_ctor_set(v___x_1284_, 0, v___x_1295_);
v___x_1297_ = v___x_1284_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_a_1279_);
v___x_1297_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v_a_1278_ = v_tail_1282_;
v_a_1279_ = v___x_1297_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1301_, lean_object* v_pos_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1301_, v_pos_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_pos_1302_);
lean_dec_ref(v_rawVal_1301_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1306_, lean_object* v_pos_1307_, lean_object* v_trailing_1308_, lean_object* v_leading_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
if (lean_obj_tag(v_a_1310_) == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_leading_1309_);
lean_dec_ref(v_trailing_1308_);
v___x_1312_ = l_List_reverse___redArg(v_a_1311_);
return v___x_1312_;
}
else
{
lean_object* v_head_1313_; lean_object* v_snd_1314_; lean_object* v_tail_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1345_; 
v_head_1313_ = lean_ctor_get(v_a_1310_, 0);
lean_inc(v_head_1313_);
v_snd_1314_ = lean_ctor_get(v_head_1313_, 1);
lean_inc(v_snd_1314_);
v_tail_1315_ = lean_ctor_get(v_a_1310_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_a_1310_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_a_1310_, 0);
lean_dec(v_unused_1346_);
v___x_1317_ = v_a_1310_;
v_isShared_1318_ = v_isSharedCheck_1345_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_tail_1315_);
lean_dec(v_a_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1345_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_fst_1319_; lean_object* v_startPos_1320_; lean_object* v_stopPos_1321_; lean_object* v_startPos_1322_; lean_object* v_stopPos_1323_; lean_object* v_off_1324_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1339_; lean_object* v___x_1342_; uint8_t v_decide_1343_; 
v_fst_1319_ = lean_ctor_get(v_head_1313_, 0);
lean_inc(v_fst_1319_);
lean_dec(v_head_1313_);
v_startPos_1320_ = lean_ctor_get(v_snd_1314_, 1);
v_stopPos_1321_ = lean_ctor_get(v_snd_1314_, 2);
v_startPos_1322_ = lean_ctor_get(v_rawVal_1306_, 1);
v_stopPos_1323_ = lean_ctor_get(v_rawVal_1306_, 2);
v_off_1324_ = lean_nat_sub(v_startPos_1320_, v_startPos_1322_);
v___x_1342_ = lean_unsigned_to_nat(0u);
v_decide_1343_ = lean_nat_dec_eq(v_off_1324_, v___x_1342_);
if (v_decide_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1339_ = v___x_1344_;
goto v___jp_1338_;
}
else
{
lean_inc_ref(v_leading_1309_);
v___y_1339_ = v_leading_1309_;
goto v___jp_1338_;
}
v___jp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_info_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1328_ = lean_nat_add(v_off_1324_, v_pos_1307_);
lean_dec(v_off_1324_);
v___x_1329_ = lean_nat_sub(v_stopPos_1321_, v_startPos_1320_);
v___x_1330_ = lean_nat_add(v___x_1329_, v___x_1328_);
lean_dec(v___x_1329_);
v_info_1331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1331_, 0, v___y_1326_);
lean_ctor_set(v_info_1331_, 1, v___x_1328_);
lean_ctor_set(v_info_1331_, 2, v___y_1327_);
lean_ctor_set(v_info_1331_, 3, v___x_1330_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1333_, 0, v_info_1331_);
lean_ctor_set(v___x_1333_, 1, v_snd_1314_);
lean_ctor_set(v___x_1333_, 2, v_fst_1319_);
lean_ctor_set(v___x_1333_, 3, v___x_1332_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_a_1311_);
lean_ctor_set(v___x_1317_, 0, v___x_1333_);
v___x_1335_ = v___x_1317_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_a_1311_);
v___x_1335_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
v_a_1310_ = v_tail_1315_;
v_a_1311_ = v___x_1335_;
goto _start;
}
}
v___jp_1338_:
{
uint8_t v_decide_1340_; 
v_decide_1340_ = lean_nat_dec_eq(v_stopPos_1321_, v_stopPos_1323_);
if (v_decide_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1326_ = v___y_1339_;
v___y_1327_ = v___x_1341_;
goto v___jp_1325_;
}
else
{
lean_inc_ref(v_trailing_1308_);
v___y_1326_ = v___y_1339_;
v___y_1327_ = v_trailing_1308_;
goto v___jp_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1347_, lean_object* v_pos_1348_, lean_object* v_trailing_1349_, lean_object* v_leading_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1347_, v_pos_1348_, v_trailing_1349_, v_leading_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_pos_1348_);
lean_dec_ref(v_rawVal_1347_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__4(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1359_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1360_ = lean_unsigned_to_nat(9u);
v___x_1361_ = lean_unsigned_to_nat(342u);
v___x_1362_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1363_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1364_ = l_mkPanicMessageWithDecl(v___x_1363_, v___x_1362_, v___x_1361_, v___x_1360_, v___x_1359_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1365_, lean_object* v_nFields_x3f_1366_){
_start:
{
if (lean_obj_tag(v_stx_1365_) == 3)
{
lean_object* v_info_1367_; 
v_info_1367_ = lean_ctor_get(v_stx_1365_, 0);
lean_inc(v_info_1367_);
if (lean_obj_tag(v_info_1367_) == 0)
{
lean_object* v_rawVal_1368_; lean_object* v_val_1369_; lean_object* v_leading_1370_; lean_object* v_pos_1371_; lean_object* v_trailing_1372_; lean_object* v_rawComps_1373_; uint8_t v___x_1374_; 
v_rawVal_1368_ = lean_ctor_get(v_stx_1365_, 1);
lean_inc_ref_n(v_rawVal_1368_, 2);
v_val_1369_ = lean_ctor_get(v_stx_1365_, 2);
lean_inc(v_val_1369_);
lean_dec_ref_known(v_stx_1365_, 4);
v_leading_1370_ = lean_ctor_get(v_info_1367_, 0);
lean_inc_ref(v_leading_1370_);
v_pos_1371_ = lean_ctor_get(v_info_1367_, 1);
lean_inc(v_pos_1371_);
v_trailing_1372_ = lean_ctor_get(v_info_1367_, 2);
lean_inc_ref(v_trailing_1372_);
lean_dec_ref_known(v_info_1367_, 4);
v_rawComps_1373_ = l_Lean_Syntax_splitNameLit(v_rawVal_1368_);
v___x_1374_ = l_List_isEmpty___redArg(v_rawComps_1373_);
if (v___x_1374_ == 0)
{
lean_object* v_val_1375_; lean_object* v_nameComps_1376_; lean_object* v___y_1378_; 
v_val_1375_ = l_Lean_Name_eraseMacroScopes(v_val_1369_);
lean_dec(v_val_1369_);
v_nameComps_1376_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1375_, v_nFields_x3f_1366_);
if (lean_obj_tag(v_nFields_x3f_1366_) == 1)
{
lean_object* v_val_1392_; lean_object* v_str_1393_; lean_object* v_startPos_1394_; lean_object* v_stopPos_1395_; lean_object* v___x_1396_; lean_object* v_nPrefix_1397_; lean_object* v___y_1399_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_prefixSz_1405_; lean_object* v___x_1406_; lean_object* v_prefixSz_1407_; lean_object* v___y_1409_; uint8_t v___x_1414_; 
v_val_1392_ = lean_ctor_get(v_nFields_x3f_1366_, 0);
v_str_1393_ = lean_ctor_get(v_rawVal_1368_, 0);
v_startPos_1394_ = lean_ctor_get(v_rawVal_1368_, 1);
v_stopPos_1395_ = lean_ctor_get(v_rawVal_1368_, 2);
v___x_1396_ = l_List_lengthTR___redArg(v_rawComps_1373_);
v_nPrefix_1397_ = lean_nat_sub(v___x_1396_, v_val_1392_);
lean_dec(v___x_1396_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1397_);
lean_inc(v_rawComps_1373_);
v___x_1404_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1373_, v_rawComps_1373_, v_nPrefix_1397_, v___x_1403_);
v_prefixSz_1405_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1402_, v___x_1404_);
lean_dec(v___x_1404_);
v___x_1406_ = lean_unsigned_to_nat(1u);
v_prefixSz_1407_ = lean_nat_sub(v_prefixSz_1405_, v___x_1406_);
lean_dec(v_prefixSz_1405_);
v___x_1414_ = lean_nat_dec_le(v_prefixSz_1407_, v___x_1402_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_le(v_stopPos_1395_, v_startPos_1394_);
if (v___x_1415_ == 0)
{
lean_inc(v_startPos_1394_);
v___y_1409_ = v_startPos_1394_;
goto v___jp_1408_;
}
else
{
lean_inc(v_stopPos_1395_);
v___y_1409_ = v_stopPos_1395_;
goto v___jp_1408_;
}
}
else
{
lean_object* v___x_1416_; 
lean_dec(v_prefixSz_1407_);
v___x_1416_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1399_ = v___x_1416_;
goto v___jp_1398_;
}
v___jp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = l_List_drop___redArg(v_nPrefix_1397_, v_rawComps_1373_);
lean_dec(v_rawComps_1373_);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___y_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___y_1378_ = v___x_1401_;
goto v___jp_1377_;
}
v___jp_1408_:
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_nat_add(v_startPos_1394_, v_prefixSz_1407_);
lean_dec(v_prefixSz_1407_);
v___x_1411_ = lean_nat_dec_le(v_stopPos_1395_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_inc_ref(v_str_1393_);
v___x_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1412_, 0, v_str_1393_);
lean_ctor_set(v___x_1412_, 1, v___y_1409_);
lean_ctor_set(v___x_1412_, 2, v___x_1410_);
v___y_1399_ = v___x_1412_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1413_; 
lean_dec(v___x_1410_);
lean_inc(v_stopPos_1395_);
lean_inc_ref(v_str_1393_);
v___x_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1413_, 0, v_str_1393_);
lean_ctor_set(v___x_1413_, 1, v___y_1409_);
lean_ctor_set(v___x_1413_, 2, v_stopPos_1395_);
v___y_1399_ = v___x_1413_;
goto v___jp_1398_;
}
}
}
else
{
v___y_1378_ = v_rawComps_1373_;
goto v___jp_1377_;
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1379_ = l_List_lengthTR___redArg(v_nameComps_1376_);
v___x_1380_ = l_List_lengthTR___redArg(v___y_1378_);
v___x_1381_ = lean_nat_dec_eq(v___x_1379_, v___x_1380_);
lean_dec(v___x_1380_);
lean_dec(v___x_1379_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v___y_1378_);
lean_dec(v_nameComps_1376_);
lean_dec_ref(v_trailing_1372_);
lean_dec(v_pos_1371_);
lean_dec_ref(v_leading_1370_);
lean_dec_ref(v_rawVal_1368_);
v___x_1382_ = lean_box(0);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_comps_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_seps_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
lean_inc(v___y_1378_);
v___x_1383_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1376_, v___y_1378_);
v___x_1384_ = lean_box(0);
v_comps_1385_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1368_, v_pos_1371_, v_trailing_1372_, v_leading_1370_, v___x_1383_, v___x_1384_);
v___x_1386_ = lean_array_mk(v___y_1378_);
v___x_1387_ = lean_array_pop(v___x_1386_);
v___x_1388_ = lean_array_to_list(v___x_1387_);
v_seps_1389_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1368_, v_pos_1371_, v___x_1388_, v___x_1384_);
lean_dec(v_pos_1371_);
lean_dec_ref(v_rawVal_1368_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_comps_1385_);
lean_ctor_set(v___x_1390_, 1, v_seps_1389_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_rawComps_1373_);
lean_dec_ref(v_trailing_1372_);
lean_dec(v_pos_1371_);
lean_dec_ref(v_leading_1370_);
lean_dec(v_val_1369_);
lean_dec_ref(v_rawVal_1368_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
}
else
{
lean_object* v___x_1418_; 
lean_dec(v_info_1367_);
lean_dec_ref_known(v_stx_1365_, 4);
v___x_1418_ = lean_box(0);
return v___x_1418_;
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec(v_stx_1365_);
v___x_1419_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__4, &l_Lean_Syntax_identComponents_x3f___closed__4_once, _init_l_Lean_Syntax_identComponents_x3f___closed__4);
v___x_1420_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1419_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1421_, lean_object* v_nFields_x3f_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Syntax_identComponents_x3f(v_stx_1421_, v_nFields_x3f_1422_);
lean_dec(v_nFields_x3f_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1424_, lean_object* v_nFields_x3f_1425_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1425_) == 1)
{
lean_object* v_val_1426_; lean_object* v_nameComps_1427_; lean_object* v___x_1428_; lean_object* v_nPrefix_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_namePrefix_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_val_1426_ = lean_ctor_get(v_nFields_x3f_1425_, 0);
v_nameComps_1427_ = l_Lean_Name_components(v_n_1424_);
v___x_1428_ = l_List_lengthTR___redArg(v_nameComps_1427_);
v_nPrefix_1429_ = lean_nat_sub(v___x_1428_, v_val_1426_);
lean_dec(v___x_1428_);
v___x_1430_ = lean_box(0);
v___x_1431_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1429_);
lean_inc(v_nameComps_1427_);
v___x_1432_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1427_, v_nameComps_1427_, v_nPrefix_1429_, v___x_1431_);
v_namePrefix_1433_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1430_, v___x_1432_);
v___x_1434_ = l_List_drop___redArg(v_nPrefix_1429_, v_nameComps_1427_);
lean_dec(v_nameComps_1427_);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_namePrefix_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Name_components(v_n_1424_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1437_, lean_object* v_nFields_x3f_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1437_, v_nFields_x3f_1438_);
lean_dec(v_nFields_x3f_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_panic_fn_borrowed(v___x_1441_, v_msg_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
if (lean_obj_tag(v_a_1444_) == 0)
{
lean_object* v___x_1446_; 
lean_dec(v_info_1443_);
v___x_1446_ = l_List_reverse___redArg(v_a_1445_);
return v___x_1446_;
}
else
{
lean_object* v_head_1447_; lean_object* v_tail_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1463_; 
v_head_1447_ = lean_ctor_get(v_a_1444_, 0);
v_tail_1448_ = lean_ctor_get(v_a_1444_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_a_1444_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1450_ = v_a_1444_;
v_isShared_1451_ = v_isSharedCheck_1463_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_tail_1448_);
lean_inc(v_head_1447_);
lean_dec(v_a_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1463_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1452_ = 1;
lean_inc(v_head_1447_);
v___x_1453_ = l_Lean_Name_toString(v_head_1447_, v___x_1452_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_string_utf8_byte_size(v___x_1453_);
v___x_1456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1453_);
lean_ctor_set(v___x_1456_, 1, v___x_1454_);
lean_ctor_set(v___x_1456_, 2, v___x_1455_);
v___x_1457_ = lean_box(0);
lean_inc(v_info_1443_);
v___x_1458_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1458_, 0, v_info_1443_);
lean_ctor_set(v___x_1458_, 1, v___x_1456_);
lean_ctor_set(v___x_1458_, 2, v_head_1447_);
lean_ctor_set(v___x_1458_, 3, v___x_1457_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v_a_1445_);
lean_ctor_set(v___x_1450_, 0, v___x_1458_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_a_1445_);
v___x_1460_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
v_a_1444_ = v_tail_1448_;
v_a_1445_ = v___x_1460_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1465_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1466_ = lean_unsigned_to_nat(9u);
v___x_1467_ = lean_unsigned_to_nat(377u);
v___x_1468_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1469_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1470_ = l_mkPanicMessageWithDecl(v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_, v___x_1465_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1471_, lean_object* v_nFields_x3f_1472_){
_start:
{
if (lean_obj_tag(v_stx_1471_) == 3)
{
lean_object* v_info_1473_; lean_object* v_rawVal_1474_; lean_object* v_val_1475_; lean_object* v_val_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_info_1473_ = lean_ctor_get(v_stx_1471_, 0);
lean_inc(v_info_1473_);
v_rawVal_1474_ = lean_ctor_get(v_stx_1471_, 1);
v_val_1475_ = lean_ctor_get(v_stx_1471_, 2);
v_val_1476_ = l_Lean_Name_eraseMacroScopes(v_val_1475_);
v___x_1477_ = l_Lean_Name_getNumParts(v_val_1476_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_dec_le(v___x_1477_, v___x_1478_);
lean_dec(v___x_1477_);
if (v___x_1479_ == 0)
{
if (lean_obj_tag(v_info_1473_) == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Syntax_identComponents_x3f(v_stx_1471_, v_nFields_x3f_1472_);
if (lean_obj_tag(v___x_1480_) == 1)
{
lean_object* v_val_1481_; lean_object* v_fst_1482_; 
lean_dec_ref_known(v_info_1473_, 4);
lean_dec(v_val_1476_);
v_val_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v_fst_1482_ = lean_ctor_get(v_val_1481_, 0);
lean_inc(v_fst_1482_);
lean_dec(v_val_1481_);
return v_fst_1482_;
}
else
{
lean_object* v_nameComps_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v___x_1480_);
v_nameComps_1483_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1476_, v_nFields_x3f_1472_);
v___x_1484_ = lean_box(0);
v___x_1485_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1473_, v_nameComps_1483_, v___x_1484_);
return v___x_1485_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref_known(v_stx_1471_, 4);
v___x_1486_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1476_, v_nFields_x3f_1472_);
v___x_1487_ = lean_box(0);
v___x_1488_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1473_, v___x_1486_, v___x_1487_);
return v___x_1488_;
}
}
else
{
lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1497_; 
lean_inc_ref(v_rawVal_1474_);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_stx_1471_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1498_ = lean_ctor_get(v_stx_1471_, 3);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_stx_1471_, 2);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_stx_1471_, 1);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_stx_1471_, 0);
lean_dec(v_unused_1501_);
v___x_1490_ = v_stx_1471_;
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v_stx_1471_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_box(0);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 3, v___x_1492_);
lean_ctor_set(v___x_1490_, 2, v_val_1476_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_info_1473_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_rawVal_1474_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_val_1476_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1492_);
return v___x_1495_;
}
}
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_stx_1471_);
v___x_1502_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1503_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1502_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1504_, lean_object* v_nFields_x3f_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Syntax_identComponents(v_stx_1504_, v_nFields_x3f_1505_);
lean_dec(v_nFields_x3f_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1507_, uint8_t v_firstChoiceOnly_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1509_, 0, v_stx_1507_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*1, v_firstChoiceOnly_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1510_, lean_object* v_firstChoiceOnly_1511_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1512_; lean_object* v_res_1513_; 
v_firstChoiceOnly_boxed_1512_ = lean_unbox(v_firstChoiceOnly_1511_);
v_res_1513_ = l_Lean_Syntax_topDown(v_stx_1510_, v_firstChoiceOnly_boxed_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1514_, lean_object* v_____r_1515_, lean_object* v_b_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_b_1516_);
v___x_1518_ = lean_apply_2(v_toPure_1514_, lean_box(0), v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1519_, lean_object* v_toPure_1520_, lean_object* v_____s_1521_){
_start:
{
lean_object* v_fst_1522_; 
v_fst_1522_ = lean_ctor_get(v_____s_1521_, 0);
if (lean_obj_tag(v_fst_1522_) == 0)
{
lean_object* v_snd_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_toPure_1520_);
v_snd_1523_ = lean_ctor_get(v_____s_1521_, 1);
lean_inc(v_snd_1523_);
lean_dec_ref(v_____s_1521_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_apply_2(v___f_1519_, v___x_1524_, v_snd_1523_);
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; lean_object* v___x_1527_; 
lean_inc_ref(v_fst_1522_);
lean_dec_ref(v_____s_1521_);
lean_dec(v___f_1519_);
v_val_1526_ = lean_ctor_get(v_fst_1522_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v_fst_1522_, 1);
v___x_1527_ = lean_apply_2(v_toPure_1520_, lean_box(0), v_val_1526_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1528_, lean_object* v_toPure_1529_, lean_object* v___x_1530_, lean_object* v_____do__lift_1531_){
_start:
{
if (lean_obj_tag(v_____do__lift_1531_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v___x_1530_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_____do__lift_1531_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_snd_1528_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
v___x_1535_ = lean_apply_2(v_toPure_1529_, lean_box(0), v___x_1534_);
return v___x_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_snd_1528_);
v_a_1536_ = lean_ctor_get(v_____do__lift_1531_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_____do__lift_1531_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1538_ = v_____do__lift_1531_;
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v_____do__lift_1531_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1530_);
lean_ctor_set(v___x_1540_, 1, v_a_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_apply_2(v_toPure_1529_, lean_box(0), v___x_1542_);
return v___x_1543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1546_, lean_object* v___x_1547_, lean_object* v_inst_1548_, lean_object* v_f_1549_, lean_object* v_firstChoiceOnly_1550_, lean_object* v_toBind_1551_, lean_object* v_a_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1555_; lean_object* v_res_1556_; 
v_firstChoiceOnly_boxed_1555_ = lean_unbox(v_firstChoiceOnly_1550_);
v_res_1556_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1546_, v___x_1547_, v_inst_1548_, v_f_1549_, v_firstChoiceOnly_boxed_1555_, v_toBind_1551_, v_a_1552_, v_x_1553_, v___y_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1560_, lean_object* v_stx_1561_, lean_object* v_inst_1562_, lean_object* v_f_1563_, uint8_t v_firstChoiceOnly_1564_, lean_object* v_toBind_1565_, lean_object* v___f_1566_, lean_object* v___x_1567_, lean_object* v___f_1568_, lean_object* v_____do__lift_1569_){
_start:
{
if (lean_obj_tag(v_____do__lift_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_dec(v___f_1568_);
lean_dec(v___f_1566_);
lean_dec(v_toBind_1565_);
lean_dec(v_f_1563_);
lean_dec_ref(v_inst_1562_);
lean_dec(v_stx_1561_);
v___x_1570_ = lean_apply_2(v_toPure_1560_, lean_box(0), v_____do__lift_1569_);
return v___x_1570_;
}
else
{
if (lean_obj_tag(v_stx_1561_) == 1)
{
lean_object* v_a_1571_; lean_object* v_kind_1572_; lean_object* v_args_1573_; 
lean_dec(v___f_1568_);
v_a_1571_ = lean_ctor_get(v_____do__lift_1569_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v_____do__lift_1569_, 1);
v_kind_1572_ = lean_ctor_get(v_stx_1561_, 1);
lean_inc(v_kind_1572_);
v_args_1573_ = lean_ctor_get(v_stx_1561_, 2);
lean_inc_ref(v_args_1573_);
lean_dec_ref_known(v_stx_1561_, 3);
if (v_firstChoiceOnly_1564_ == 0)
{
lean_dec(v_kind_1572_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1584_ = lean_name_eq(v_kind_1572_, v___x_1583_);
lean_dec(v_kind_1572_);
if (v___x_1584_ == 0)
{
goto v___jp_1574_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v___f_1566_);
lean_dec(v_toBind_1565_);
lean_dec(v_toPure_1560_);
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = lean_array_get(v___x_1567_, v_args_1573_, v___x_1585_);
lean_dec_ref(v_args_1573_);
v___x_1587_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1562_, v_f_1563_, v_firstChoiceOnly_1564_, v___x_1586_, v_a_1571_);
return v___x_1587_;
}
}
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; size_t v_sz_1579_; size_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_box(v_firstChoiceOnly_1564_);
lean_inc(v_toBind_1565_);
lean_inc_ref(v_inst_1562_);
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1577_, 0, v_toPure_1560_);
lean_closure_set(v___f_1577_, 1, v___x_1575_);
lean_closure_set(v___f_1577_, 2, v_inst_1562_);
lean_closure_set(v___f_1577_, 3, v_f_1563_);
lean_closure_set(v___f_1577_, 4, v___x_1576_);
lean_closure_set(v___f_1577_, 5, v_toBind_1565_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1575_);
lean_ctor_set(v___x_1578_, 1, v_a_1571_);
v_sz_1579_ = lean_array_size(v_args_1573_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1562_, v_args_1573_, v___f_1577_, v_sz_1579_, v___x_1580_, v___x_1578_);
v___x_1582_ = lean_apply_4(v_toBind_1565_, lean_box(0), lean_box(0), v___x_1581_, v___f_1566_);
return v___x_1582_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v___f_1566_);
lean_dec(v_toBind_1565_);
lean_dec(v_f_1563_);
lean_dec_ref(v_inst_1562_);
lean_dec(v_stx_1561_);
lean_dec(v_toPure_1560_);
v_a_1588_ = lean_ctor_get(v_____do__lift_1569_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v_____do__lift_1569_, 1);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_apply_2(v___f_1568_, v___x_1589_, v_a_1588_);
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1591_, lean_object* v_stx_1592_, lean_object* v_inst_1593_, lean_object* v_f_1594_, lean_object* v_firstChoiceOnly_1595_, lean_object* v_toBind_1596_, lean_object* v___f_1597_, lean_object* v___x_1598_, lean_object* v___f_1599_, lean_object* v_____do__lift_1600_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1601_; lean_object* v_res_1602_; 
v_firstChoiceOnly_boxed_1601_ = lean_unbox(v_firstChoiceOnly_1595_);
v_res_1602_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1591_, v_stx_1592_, v_inst_1593_, v_f_1594_, v_firstChoiceOnly_boxed_1601_, v_toBind_1596_, v___f_1597_, v___x_1598_, v___f_1599_, v_____do__lift_1600_);
lean_dec(v___x_1598_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1603_, lean_object* v_f_1604_, uint8_t v_firstChoiceOnly_1605_, lean_object* v_stx_1606_, lean_object* v_b_1607_){
_start:
{
lean_object* v_toApplicative_1608_; lean_object* v_toBind_1609_; lean_object* v_toPure_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___f_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; 
v_toApplicative_1608_ = lean_ctor_get(v_inst_1603_, 0);
v_toBind_1609_ = lean_ctor_get(v_inst_1603_, 1);
lean_inc_n(v_toBind_1609_, 2);
v_toPure_1610_ = lean_ctor_get(v_toApplicative_1608_, 1);
lean_inc_n(v_toPure_1610_, 3);
v___x_1611_ = lean_box(0);
lean_inc(v_f_1604_);
lean_inc(v_stx_1606_);
v___x_1612_ = lean_apply_2(v_f_1604_, v_stx_1606_, v_b_1607_);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1613_, 0, v_toPure_1610_);
lean_inc_ref(v___f_1613_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1614_, 0, v___f_1613_);
lean_closure_set(v___f_1614_, 1, v_toPure_1610_);
v___x_1615_ = lean_box(v_firstChoiceOnly_1605_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1616_, 0, v_toPure_1610_);
lean_closure_set(v___f_1616_, 1, v_stx_1606_);
lean_closure_set(v___f_1616_, 2, v_inst_1603_);
lean_closure_set(v___f_1616_, 3, v_f_1604_);
lean_closure_set(v___f_1616_, 4, v___x_1615_);
lean_closure_set(v___f_1616_, 5, v_toBind_1609_);
lean_closure_set(v___f_1616_, 6, v___f_1614_);
lean_closure_set(v___f_1616_, 7, v___x_1611_);
lean_closure_set(v___f_1616_, 8, v___f_1613_);
v___x_1617_ = lean_apply_4(v_toBind_1609_, lean_box(0), lean_box(0), v___x_1612_, v___f_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1618_, lean_object* v___x_1619_, lean_object* v_inst_1620_, lean_object* v_f_1621_, uint8_t v_firstChoiceOnly_1622_, lean_object* v_toBind_1623_, lean_object* v_a_1624_, lean_object* v_x_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_snd_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_snd_1627_ = lean_ctor_get(v___y_1626_, 1);
lean_inc_n(v_snd_1627_, 2);
lean_dec_ref(v___y_1626_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1628_, 0, v_snd_1627_);
lean_closure_set(v___f_1628_, 1, v_toPure_1618_);
lean_closure_set(v___f_1628_, 2, v___x_1619_);
v___x_1629_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1620_, v_f_1621_, v_firstChoiceOnly_1622_, v_a_1624_, v_snd_1627_);
v___x_1630_ = lean_apply_4(v_toBind_1623_, lean_box(0), lean_box(0), v___x_1629_, v___f_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1631_, lean_object* v_f_1632_, lean_object* v_firstChoiceOnly_1633_, lean_object* v_stx_1634_, lean_object* v_b_1635_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1636_; lean_object* v_res_1637_; 
v_firstChoiceOnly_boxed_1636_ = lean_unbox(v_firstChoiceOnly_1633_);
v_res_1637_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1631_, v_f_1632_, v_firstChoiceOnly_boxed_1636_, v_stx_1634_, v_b_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1638_, lean_object* v_inst_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_f_1641_, uint8_t v_firstChoiceOnly_1642_, lean_object* v_stx_1643_, lean_object* v_b_1644_, lean_object* v_inst_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1639_, v_f_1641_, v_firstChoiceOnly_1642_, v_stx_1643_, v_b_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1647_, lean_object* v_inst_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_f_1650_, lean_object* v_firstChoiceOnly_1651_, lean_object* v_stx_1652_, lean_object* v_b_1653_, lean_object* v_inst_1654_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1655_; lean_object* v_res_1656_; 
v_firstChoiceOnly_boxed_1655_ = lean_unbox(v_firstChoiceOnly_1651_);
v_res_1656_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1647_, v_inst_1648_, v_00_u03b2_1649_, v_f_1650_, v_firstChoiceOnly_boxed_1655_, v_stx_1652_, v_b_1653_, v_inst_1654_);
lean_dec(v_inst_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1657_, lean_object* v_____do__lift_1658_){
_start:
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v_____do__lift_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v_____do__lift_1658_);
v___x_1660_ = lean_apply_2(v_toPure_1657_, lean_box(0), v_a_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1661_, lean_object* v_toBind_1662_, lean_object* v___f_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_x_1665_, lean_object* v_init_1666_, lean_object* v_f_1667_){
_start:
{
uint8_t v_firstChoiceOnly_1668_; lean_object* v_stx_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_firstChoiceOnly_1668_ = lean_ctor_get_uint8(v_x_1665_, sizeof(void*)*1);
v_stx_1669_ = lean_ctor_get(v_x_1665_, 0);
lean_inc(v_stx_1669_);
lean_dec_ref(v_x_1665_);
v___x_1670_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1661_, v_f_1667_, v_firstChoiceOnly_1668_, v_stx_1669_, v_init_1666_);
v___x_1671_ = lean_apply_4(v_toBind_1662_, lean_box(0), lean_box(0), v___x_1670_, v___f_1663_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1672_){
_start:
{
lean_object* v_toApplicative_1673_; lean_object* v_toBind_1674_; lean_object* v_toPure_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; 
v_toApplicative_1673_ = lean_ctor_get(v_inst_1672_, 0);
v_toBind_1674_ = lean_ctor_get(v_inst_1672_, 1);
lean_inc(v_toBind_1674_);
v_toPure_1675_ = lean_ctor_get(v_toApplicative_1673_, 1);
lean_inc(v_toPure_1675_);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1676_, 0, v_toPure_1675_);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1677_, 0, v_inst_1672_);
lean_closure_set(v___f_1677_, 1, v_toBind_1674_);
lean_closure_set(v___f_1677_, 2, v___f_1676_);
return v___f_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1678_, lean_object* v_inst_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1682_, lean_object* v_val_1683_){
_start:
{
if (lean_obj_tag(v_info_1682_) == 0)
{
lean_object* v_leading_1684_; lean_object* v_trailing_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_leading_1684_ = lean_ctor_get(v_info_1682_, 0);
lean_inc_ref(v_leading_1684_);
v_trailing_1685_ = lean_ctor_get(v_info_1682_, 2);
lean_inc_ref(v_trailing_1685_);
lean_dec_ref_known(v_info_1682_, 4);
v___x_1686_ = lean_substring_tostring(v_leading_1684_);
v___x_1687_ = lean_string_append(v___x_1686_, v_val_1683_);
v___x_1688_ = lean_substring_tostring(v_trailing_1685_);
v___x_1689_ = lean_string_append(v___x_1687_, v___x_1688_);
lean_dec_ref(v___x_1688_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_info_1682_);
v___x_1690_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1691_ = lean_string_append(v___x_1690_, v_val_1683_);
v___x_1692_ = lean_string_append(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1693_, lean_object* v_val_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1693_, v_val_1694_);
lean_dec_ref(v_val_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1696_, lean_object* v_as_1697_, size_t v_sz_1698_, size_t v_i_1699_, lean_object* v_b_1700_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_lt(v_i_1699_, v_sz_1698_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_b_1700_);
return v___x_1702_;
}
else
{
lean_object* v_snd_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1730_; 
v_snd_1703_ = lean_ctor_get(v_b_1700_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_b_1700_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v_b_1700_, 0);
lean_dec(v_unused_1731_);
v___x_1705_ = v_b_1700_;
v_isShared_1706_ = v_isSharedCheck_1730_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_snd_1703_);
lean_dec(v_b_1700_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1730_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_a_1707_; lean_object* v___x_1708_; 
v_a_1707_ = lean_array_uget_borrowed(v_as_1697_, v_i_1699_);
lean_inc(v_snd_1703_);
lean_inc(v_a_1707_);
v___x_1708_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1696_, v_a_1707_, v_snd_1703_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_del_object(v___x_1705_);
lean_dec(v_snd_1703_);
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
else
{
lean_object* v_val_1710_; 
v_val_1710_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1710_);
if (lean_obj_tag(v_val_1710_) == 0)
{
lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1720_; 
v_isSharedCheck_1720_ = !lean_is_exclusive(v_val_1710_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v_val_1710_, 0);
lean_dec(v_unused_1721_);
v___x_1712_ = v_val_1710_;
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v_val_1710_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1708_);
v___x_1715_ = v___x_1705_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_snd_1703_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 1);
lean_ctor_set(v___x_1712_, 0, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
lean_dec_ref_known(v___x_1708_, 1);
lean_dec(v_snd_1703_);
v_a_1722_ = lean_ctor_get(v_val_1710_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v_val_1710_, 1);
v___x_1723_ = lean_box(0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_a_1722_);
lean_ctor_set(v___x_1705_, 0, v___x_1723_);
v___x_1725_ = v___x_1705_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_a_1722_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
size_t v___x_1726_; size_t v___x_1727_; 
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1699_, v___x_1726_);
v_i_1699_ = v___x_1727_;
v_b_1700_ = v___x_1725_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1732_, lean_object* v_a_1733_, lean_object* v_b_1734_){
_start:
{
lean_object* v_array_1735_; lean_object* v_start_1736_; lean_object* v_stop_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1756_; 
v_array_1735_ = lean_ctor_get(v_a_1733_, 0);
v_start_1736_ = lean_ctor_get(v_a_1733_, 1);
v_stop_1737_ = lean_ctor_get(v_a_1733_, 2);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_a_1733_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1739_ = v_a_1733_;
v_isShared_1740_ = v_isSharedCheck_1756_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_stop_1737_);
lean_inc(v_start_1736_);
lean_inc(v_array_1735_);
lean_dec(v_a_1733_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1756_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_lt(v_start_1736_, v_stop_1737_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_del_object(v___x_1739_);
lean_dec(v_stop_1737_);
lean_dec(v_start_1736_);
lean_dec_ref(v_array_1735_);
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_b_1734_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_array_fget_borrowed(v_array_1735_, v_start_1736_);
lean_inc(v___x_1743_);
v___x_1744_ = l_Lean_Syntax_reprint(v___x_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
lean_del_object(v___x_1739_);
lean_dec(v_stop_1737_);
lean_dec(v_start_1736_);
lean_dec_ref(v_array_1735_);
v___x_1745_ = lean_box(0);
return v___x_1745_;
}
else
{
lean_object* v_val_1746_; uint8_t v___x_1747_; 
v_val_1746_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1747_ = lean_string_dec_eq(v_val_1732_, v_val_1746_);
lean_dec(v_val_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_del_object(v___x_1739_);
lean_dec(v_stop_1737_);
lean_dec(v_start_1736_);
lean_dec_ref(v_array_1735_);
v___x_1748_ = lean_box(0);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1749_ = lean_box(0);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_start_1736_, v___x_1750_);
lean_dec(v_start_1736_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1751_);
v___x_1753_ = v___x_1739_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_array_1735_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_stop_1737_);
v___x_1753_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
v_a_1733_ = v___x_1753_;
v_b_1734_ = v___x_1749_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1757_, lean_object* v_stx_1758_, lean_object* v_b_1759_){
_start:
{
lean_object* v_b_1761_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___x_1775_; lean_object* v_a_1777_; 
v___x_1775_ = lean_box(0);
switch(lean_obj_tag(v_stx_1758_))
{
case 2:
{
lean_object* v_info_1786_; lean_object* v_val_1787_; lean_object* v___x_1788_; lean_object* v_s_1789_; 
v_info_1786_ = lean_ctor_get(v_stx_1758_, 0);
v_val_1787_ = lean_ctor_get(v_stx_1758_, 1);
lean_inc(v_info_1786_);
v___x_1788_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1786_, v_val_1787_);
v_s_1789_ = lean_string_append(v_b_1759_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v_a_1777_ = v_s_1789_;
goto v___jp_1776_;
}
case 3:
{
lean_object* v_rawVal_1790_; lean_object* v_info_1791_; lean_object* v_str_1792_; lean_object* v_startPos_1793_; lean_object* v_stopPos_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_s_1797_; 
v_rawVal_1790_ = lean_ctor_get(v_stx_1758_, 1);
v_info_1791_ = lean_ctor_get(v_stx_1758_, 0);
v_str_1792_ = lean_ctor_get(v_rawVal_1790_, 0);
v_startPos_1793_ = lean_ctor_get(v_rawVal_1790_, 1);
v_stopPos_1794_ = lean_ctor_get(v_rawVal_1790_, 2);
v___x_1795_ = lean_string_utf8_extract(v_str_1792_, v_startPos_1793_, v_stopPos_1794_);
lean_inc(v_info_1791_);
v___x_1796_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1791_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v_s_1797_ = lean_string_append(v_b_1759_, v___x_1796_);
lean_dec_ref(v___x_1796_);
v_a_1777_ = v_s_1797_;
goto v___jp_1776_;
}
case 1:
{
lean_object* v_kind_1798_; lean_object* v_args_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_kind_1798_ = lean_ctor_get(v_stx_1758_, 1);
v_args_1799_ = lean_ctor_get(v_stx_1758_, 2);
v___x_1800_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1801_ = lean_name_eq(v_kind_1798_, v___x_1800_);
if (v___x_1801_ == 0)
{
v_a_1777_ = v_b_1759_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_array_get_borrowed(v___x_1775_, v_args_1799_, v___x_1802_);
lean_inc(v___x_1803_);
v___x_1804_ = l_Lean_Syntax_reprint(v___x_1803_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref_known(v_stx_1758_, 3);
lean_dec_ref(v_b_1759_);
v___x_1805_ = lean_box(0);
return v___x_1805_;
}
else
{
lean_object* v_val_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_val_1806_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1806_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_array_get_size(v_args_1799_);
lean_inc_ref(v_args_1799_);
v___x_1809_ = l_Array_toSubarray___redArg(v_args_1799_, v___x_1807_, v___x_1808_);
v___x_1810_ = lean_box(0);
v___x_1811_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1806_, v___x_1809_, v___x_1810_);
lean_dec(v_val_1806_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; 
lean_dec_ref_known(v_stx_1758_, 3);
lean_dec_ref(v_b_1759_);
v___x_1812_ = lean_box(0);
return v___x_1812_;
}
else
{
lean_dec_ref_known(v___x_1811_, 1);
v_a_1777_ = v_b_1759_;
goto v___jp_1776_;
}
}
}
}
default: 
{
v_a_1777_ = v_b_1759_;
goto v___jp_1776_;
}
}
v___jp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_b_1761_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
v___jp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; size_t v_sz_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1767_ = lean_box(0);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___y_1765_);
v_sz_1769_ = lean_array_size(v___y_1766_);
v___x_1770_ = ((size_t)0ULL);
v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1757_, v___y_1766_, v_sz_1769_, v___x_1770_, v___x_1768_);
lean_dec_ref(v___y_1766_);
if (lean_obj_tag(v___x_1771_) == 0)
{
return v___x_1767_;
}
else
{
lean_object* v_val_1772_; lean_object* v_fst_1773_; 
v_val_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v_fst_1773_ = lean_ctor_get(v_val_1772_, 0);
if (lean_obj_tag(v_fst_1773_) == 0)
{
lean_object* v_snd_1774_; 
v_snd_1774_ = lean_ctor_get(v_val_1772_, 1);
lean_inc(v_snd_1774_);
lean_dec(v_val_1772_);
v_b_1761_ = v_snd_1774_;
goto v___jp_1760_;
}
else
{
lean_inc_ref(v_fst_1773_);
lean_dec(v_val_1772_);
return v_fst_1773_;
}
}
}
v___jp_1776_:
{
if (lean_obj_tag(v_stx_1758_) == 1)
{
if (v_firstChoiceOnly_1757_ == 0)
{
lean_object* v_args_1778_; 
v_args_1778_ = lean_ctor_get(v_stx_1758_, 2);
lean_inc_ref(v_args_1778_);
lean_dec_ref_known(v_stx_1758_, 3);
v___y_1765_ = v_a_1777_;
v___y_1766_ = v_args_1778_;
goto v___jp_1764_;
}
else
{
lean_object* v_kind_1779_; lean_object* v_args_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_kind_1779_ = lean_ctor_get(v_stx_1758_, 1);
lean_inc(v_kind_1779_);
v_args_1780_ = lean_ctor_get(v_stx_1758_, 2);
lean_inc_ref(v_args_1780_);
lean_dec_ref_known(v_stx_1758_, 3);
v___x_1781_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1782_ = lean_name_eq(v_kind_1779_, v___x_1781_);
lean_dec(v_kind_1779_);
if (v___x_1782_ == 0)
{
v___y_1765_ = v_a_1777_;
v___y_1766_ = v_args_1780_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_array_get(v___x_1775_, v_args_1780_, v___x_1783_);
lean_dec_ref(v_args_1780_);
v_stx_1758_ = v___x_1784_;
v_b_1759_ = v_a_1777_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1758_);
v_b_1761_ = v_a_1777_;
goto v___jp_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1813_){
_start:
{
lean_object* v_s_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; 
v_s_1814_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1815_ = 1;
v___x_1816_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1815_, v_stx_1813_, v_s_1814_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_box(0);
return v___x_1817_;
}
else
{
lean_object* v_val_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1826_; 
v_val_1818_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1820_ = v___x_1816_;
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_val_1818_);
lean_dec(v___x_1816_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_a_1822_; lean_object* v___x_1824_; 
v_a_1822_ = lean_ctor_get(v_val_1818_, 0);
lean_inc(v_a_1822_);
lean_dec(v_val_1818_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1822_);
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1827_, lean_object* v_a_1828_, lean_object* v_b_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1827_, v_a_1828_, v_b_1829_);
lean_dec_ref(v_val_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1831_, lean_object* v_as_1832_, lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_b_1835_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1836_; size_t v_sz_boxed_1837_; size_t v_i_boxed_1838_; lean_object* v_res_1839_; 
v_firstChoiceOnly_boxed_1836_ = lean_unbox(v_firstChoiceOnly_1831_);
v_sz_boxed_1837_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1838_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1836_, v_as_1832_, v_sz_boxed_1837_, v_i_boxed_1838_, v_b_1835_);
lean_dec_ref(v_as_1832_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1840_, lean_object* v_stx_1841_, lean_object* v_b_1842_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1843_; lean_object* v_res_1844_; 
v_firstChoiceOnly_boxed_1843_ = lean_unbox(v_firstChoiceOnly_1840_);
v_res_1844_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1843_, v_stx_1841_, v_b_1842_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1845_, lean_object* v_inst_1846_, lean_object* v_R_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v_c_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1845_, v_a_1848_, v_b_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1852_, lean_object* v_inst_1853_, lean_object* v_R_1854_, lean_object* v_a_1855_, lean_object* v_b_1856_, lean_object* v_c_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1852_, v_inst_1853_, v_R_1854_, v_a_1855_, v_b_1856_, v_c_1857_);
lean_dec_ref(v_val_1852_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1867_, lean_object* v_stx_1868_){
_start:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = l_Lean_Syntax_isMissing(v_stx_1868_);
if (v___x_1870_ == 0)
{
if (lean_obj_tag(v_stx_1868_) == 1)
{
lean_object* v_kind_1871_; lean_object* v_args_1872_; 
v_kind_1871_ = lean_ctor_get(v_stx_1868_, 1);
v_args_1872_ = lean_ctor_get(v_stx_1868_, 2);
if (v_firstChoiceOnly_1867_ == 0)
{
goto v___jp_1873_;
}
else
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1883_ = lean_name_eq(v_kind_1871_, v___x_1882_);
if (v___x_1883_ == 0)
{
goto v___jp_1873_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_get_borrowed(v___x_1884_, v_args_1872_, v___x_1885_);
v_stx_1868_ = v___x_1886_;
goto _start;
}
}
v___jp_1873_:
{
lean_object* v___x_1874_; size_t v_sz_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v_fst_1878_; 
v___x_1874_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1875_ = lean_array_size(v_args_1872_);
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1867_, v_args_1872_, v_sz_1875_, v___x_1876_, v___x_1874_);
v_fst_1878_ = lean_ctor_get(v___x_1877_, 0);
if (lean_obj_tag(v_fst_1878_) == 0)
{
lean_object* v_snd_1879_; lean_object* v___x_1880_; 
v_snd_1879_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_snd_1879_);
lean_dec_ref(v___x_1877_);
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_snd_1879_);
return v___x_1880_;
}
else
{
lean_object* v_val_1881_; 
lean_inc_ref(v_fst_1878_);
lean_dec_ref(v___x_1877_);
v_val_1881_ = lean_ctor_get(v_fst_1878_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v_fst_1878_, 1);
return v_val_1881_;
}
}
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1888_;
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_box(v___x_1870_);
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1869_);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1893_, lean_object* v_as_1894_, size_t v_sz_1895_, size_t v_i_1896_, lean_object* v_b_1897_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1896_, v_sz_1895_);
if (v___x_1898_ == 0)
{
return v_b_1897_;
}
else
{
lean_object* v_snd_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1917_; 
v_snd_1899_ = lean_ctor_get(v_b_1897_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_b_1897_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_b_1897_, 0);
lean_dec(v_unused_1918_);
v___x_1901_ = v_b_1897_;
v_isShared_1902_ = v_isSharedCheck_1917_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snd_1899_);
lean_dec(v_b_1897_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1917_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_array_uget_borrowed(v_as_1894_, v_i_1896_);
v___x_1904_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1893_, v_a_1903_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1905_);
v___x_1907_ = v___x_1901_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_snd_1899_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec(v_snd_1899_);
v_a_1909_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1910_ = lean_box(0);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v_a_1909_);
lean_ctor_set(v___x_1901_, 0, v___x_1910_);
v___x_1912_ = v___x_1901_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1909_);
v___x_1912_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
size_t v___x_1913_; size_t v___x_1914_; 
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1896_, v___x_1913_);
v_i_1896_ = v___x_1914_;
v_b_1897_ = v___x_1912_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1919_, lean_object* v_as_1920_, lean_object* v_sz_1921_, lean_object* v_i_1922_, lean_object* v_b_1923_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1924_; size_t v_sz_boxed_1925_; size_t v_i_boxed_1926_; lean_object* v_res_1927_; 
v_firstChoiceOnly_boxed_1924_ = lean_unbox(v_firstChoiceOnly_1919_);
v_sz_boxed_1925_ = lean_unbox_usize(v_sz_1921_);
lean_dec(v_sz_1921_);
v_i_boxed_1926_ = lean_unbox_usize(v_i_1922_);
lean_dec(v_i_1922_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1924_, v_as_1920_, v_sz_boxed_1925_, v_i_boxed_1926_, v_b_1923_);
lean_dec_ref(v_as_1920_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1928_, lean_object* v_stx_1929_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1930_; lean_object* v_res_1931_; 
v_firstChoiceOnly_boxed_1930_ = lean_unbox(v_firstChoiceOnly_1928_);
v_res_1931_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1930_, v_stx_1929_);
lean_dec(v_stx_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1932_){
_start:
{
uint8_t v___x_1933_; lean_object* v___y_1935_; lean_object* v___x_1939_; lean_object* v_a_1940_; 
v___x_1933_ = 0;
v___x_1939_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1933_, v_stx_1932_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___y_1935_ = v_a_1940_;
goto v___jp_1934_;
v___jp_1934_:
{
lean_object* v_fst_1936_; 
v_fst_1936_ = lean_ctor_get(v___y_1935_, 0);
lean_inc(v_fst_1936_);
lean_dec_ref(v___y_1935_);
if (lean_obj_tag(v_fst_1936_) == 0)
{
return v___x_1933_;
}
else
{
lean_object* v_val_1937_; uint8_t v___x_1938_; 
v_val_1937_ = lean_ctor_get(v_fst_1936_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_fst_1936_, 1);
v___x_1938_ = lean_unbox(v_val_1937_);
lean_dec(v_val_1937_);
return v___x_1938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1941_){
_start:
{
uint8_t v_res_1942_; lean_object* v_r_1943_; 
v_res_1942_ = l_Lean_Syntax_hasMissing(v_stx_1941_);
lean_dec(v_stx_1941_);
v_r_1943_ = lean_box(v_res_1942_);
return v_r_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1944_, lean_object* v_stx_1945_, lean_object* v_b_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1944_, v_stx_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1948_, lean_object* v_stx_1949_, lean_object* v_b_1950_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1951_; lean_object* v_res_1952_; 
v_firstChoiceOnly_boxed_1951_ = lean_unbox(v_firstChoiceOnly_1948_);
v_res_1952_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1951_, v_stx_1949_, v_b_1950_);
lean_dec_ref(v_b_1950_);
lean_dec(v_stx_1949_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1953_, uint8_t v_canonicalOnly_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_Syntax_getPos_x3f(v_stx_1953_, v_canonicalOnly_1954_);
if (lean_obj_tag(v___x_1955_) == 1)
{
lean_object* v_val_1956_; lean_object* v___x_1957_; 
v_val_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_val_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1953_, v_canonicalOnly_1954_);
if (lean_obj_tag(v___x_1957_) == 1)
{
lean_object* v_val_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1966_; 
v_val_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1966_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_val_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1966_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_val_1956_);
lean_ctor_set(v___x_1962_, 1, v_val_1958_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1962_);
v___x_1964_ = v___x_1960_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v___x_1967_; 
lean_dec(v___x_1957_);
lean_dec(v_val_1956_);
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
}
else
{
lean_object* v___x_1968_; 
lean_dec(v___x_1955_);
v___x_1968_ = lean_box(0);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1969_, lean_object* v_canonicalOnly_1970_){
_start:
{
uint8_t v_canonicalOnly_boxed_1971_; lean_object* v_res_1972_; 
v_canonicalOnly_boxed_1971_ = lean_unbox(v_canonicalOnly_1970_);
v_res_1972_ = l_Lean_Syntax_getRange_x3f(v_stx_1969_, v_canonicalOnly_boxed_1971_);
lean_dec(v_stx_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1973_, uint8_t v_canonicalOnly_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Syntax_getPos_x3f(v_stx_1973_, v_canonicalOnly_1974_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_box(0);
return v___x_1976_;
}
else
{
lean_object* v_val_1977_; lean_object* v___x_1978_; 
v_val_1977_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_val_1977_);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1978_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1973_, v_canonicalOnly_1974_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1979_; 
lean_dec(v_val_1977_);
v___x_1979_ = lean_box(0);
return v___x_1979_;
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_val_1980_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v___x_1978_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_val_1980_);
lean_dec(v___x_1978_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_val_1977_);
lean_ctor_set(v___x_1984_, 1, v_val_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1989_, lean_object* v_canonicalOnly_1990_){
_start:
{
uint8_t v_canonicalOnly_boxed_1991_; lean_object* v_res_1992_; 
v_canonicalOnly_boxed_1991_ = lean_unbox(v_canonicalOnly_1990_);
v_res_1992_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1989_, v_canonicalOnly_boxed_1991_);
lean_dec(v_stx_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1993_, uint8_t v_canonical_1994_){
_start:
{
lean_object* v_start_1995_; lean_object* v_stop_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2005_; 
v_start_1995_ = lean_ctor_get(v_range_1993_, 0);
v_stop_1996_ = lean_ctor_get(v_range_1993_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_range_1993_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1998_ = v_range_1993_;
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_stop_1996_);
lean_inc(v_start_1995_);
lean_dec(v_range_1993_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2000_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2000_, 0, v_start_1995_);
lean_ctor_set(v___x_2000_, 1, v_stop_1996_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*2, v_canonical_1994_);
v___x_2001_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 2);
lean_ctor_set(v___x_1998_, 1, v___x_2001_);
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2003_ = v___x_1998_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2006_, lean_object* v_canonical_2007_){
_start:
{
uint8_t v_canonical_boxed_2008_; lean_object* v_res_2009_; 
v_canonical_boxed_2008_ = lean_unbox(v_canonical_2007_);
v_res_2009_ = l_Lean_Syntax_ofRange(v_range_2006_, v_canonical_boxed_2008_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2014_, 0, v_stx_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
lean_ctor_set(v___x_2014_, 2, v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2015_, lean_object* v_stx_2016_){
_start:
{
lean_object* v_parents_2017_; lean_object* v_idxs_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_parents_2017_ = lean_ctor_get(v_t_2015_, 1);
v_idxs_2018_ = lean_ctor_get(v_t_2015_, 2);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_t_2015_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v_t_2015_, 0);
lean_dec(v_unused_2026_);
v___x_2020_ = v_t_2015_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_idxs_2018_);
lean_inc(v_parents_2017_);
lean_dec(v_t_2015_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v_stx_2016_);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_stx_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_parents_2017_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_idxs_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2027_, lean_object* v_idx_2028_){
_start:
{
lean_object* v_cur_2029_; lean_object* v_parents_2030_; lean_object* v_idxs_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2051_; 
v_cur_2029_ = lean_ctor_get(v_t_2027_, 0);
v_parents_2030_ = lean_ctor_get(v_t_2027_, 1);
v_idxs_2031_ = lean_ctor_get(v_t_2027_, 2);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_t_2027_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2033_ = v_t_2027_;
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_idxs_2031_);
lean_inc(v_parents_2030_);
lean_inc(v_cur_2029_);
lean_dec(v_t_2027_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = l_Lean_Syntax_getNumArgs(v_cur_2029_);
v___x_2036_ = lean_nat_dec_lt(v_idx_2028_, v___x_2035_);
lean_dec(v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_array_push(v_parents_2030_, v_cur_2029_);
v___x_2039_ = lean_array_push(v_idxs_2031_, v_idx_2028_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 2, v___x_2039_);
lean_ctor_set(v___x_2033_, 1, v___x_2038_);
lean_ctor_set(v___x_2033_, 0, v___x_2037_);
v___x_2041_ = v___x_2033_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2043_ = l_Lean_Syntax_getArg(v_cur_2029_, v_idx_2028_);
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_Syntax_setArg(v_cur_2029_, v_idx_2028_, v___x_2044_);
v___x_2046_ = lean_array_push(v_parents_2030_, v___x_2045_);
v___x_2047_ = lean_array_push(v_idxs_2031_, v_idx_2028_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 2, v___x_2047_);
lean_ctor_set(v___x_2033_, 1, v___x_2046_);
lean_ctor_set(v___x_2033_, 0, v___x_2043_);
v___x_2049_ = v___x_2033_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2043_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2052_){
_start:
{
lean_object* v_cur_2053_; lean_object* v_parents_2054_; lean_object* v_idxs_2055_; lean_object* v___y_2057_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_cur_2053_ = lean_ctor_get(v_t_2052_, 0);
v_parents_2054_ = lean_ctor_get(v_t_2052_, 1);
v_idxs_2055_ = lean_ctor_get(v_t_2052_, 2);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_array_get_size(v_parents_2054_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
return v_t_2052_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
lean_inc_ref(v_idxs_2055_);
lean_inc_ref(v_parents_2054_);
lean_inc(v_cur_2053_);
lean_dec_ref(v_t_2052_);
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_array_get_size(v_idxs_2055_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_sub(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_array_get_borrowed(v___x_2061_, v_idxs_2055_, v___x_2067_);
lean_dec(v___x_2067_);
v___x_2069_ = lean_nat_sub(v___x_2062_, v___x_2066_);
v___x_2070_ = lean_array_get_borrowed(v___x_2064_, v_parents_2054_, v___x_2069_);
lean_dec(v___x_2069_);
v___x_2071_ = l_Lean_Syntax_getNumArgs(v___x_2070_);
v___x_2072_ = lean_nat_dec_lt(v___x_2068_, v___x_2071_);
lean_dec(v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v_cur_2053_);
lean_inc(v___x_2070_);
v___y_2057_ = v___x_2070_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2073_; 
lean_inc(v___x_2070_);
v___x_2073_ = l_Lean_Syntax_setArg(v___x_2070_, v___x_2068_, v_cur_2053_);
v___y_2057_ = v___x_2073_;
goto v___jp_2056_;
}
}
v___jp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_array_pop(v_parents_2054_);
v___x_2059_ = lean_array_pop(v_idxs_2055_);
v___x_2060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2057_);
lean_ctor_set(v___x_2060_, 1, v___x_2058_);
lean_ctor_set(v___x_2060_, 2, v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2074_){
_start:
{
lean_object* v_parents_2075_; lean_object* v_idxs_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_parents_2075_ = lean_ctor_get(v_t_2074_, 1);
v_idxs_2076_ = lean_ctor_get(v_t_2074_, 2);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_array_get_size(v_parents_2075_);
v___x_2079_ = lean_nat_dec_lt(v___x_2077_, v___x_2078_);
if (v___x_2079_ == 0)
{
return v_t_2074_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_inc_ref(v_idxs_2076_);
v___x_2080_ = l_Lean_Syntax_Traverser_up(v_t_2074_);
v___x_2081_ = lean_array_get_size(v_idxs_2076_);
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_nat_sub(v___x_2081_, v___x_2082_);
v___x_2084_ = lean_array_get(v___x_2077_, v_idxs_2076_, v___x_2083_);
lean_dec(v___x_2083_);
lean_dec_ref(v_idxs_2076_);
v___x_2085_ = lean_nat_sub(v___x_2084_, v___x_2082_);
lean_dec(v___x_2084_);
v___x_2086_ = l_Lean_Syntax_Traverser_down(v___x_2080_, v___x_2085_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2087_){
_start:
{
lean_object* v_parents_2088_; lean_object* v_idxs_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_parents_2088_ = lean_ctor_get(v_t_2087_, 1);
v_idxs_2089_ = lean_ctor_get(v_t_2087_, 2);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_array_get_size(v_parents_2088_);
v___x_2092_ = lean_nat_dec_lt(v___x_2090_, v___x_2091_);
if (v___x_2092_ == 0)
{
return v_t_2087_;
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_inc_ref(v_idxs_2089_);
v___x_2093_ = l_Lean_Syntax_Traverser_up(v_t_2087_);
v___x_2094_ = lean_array_get_size(v_idxs_2089_);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = lean_nat_sub(v___x_2094_, v___x_2095_);
v___x_2097_ = lean_array_get(v___x_2090_, v_idxs_2089_, v___x_2096_);
lean_dec(v___x_2096_);
lean_dec_ref(v_idxs_2089_);
v___x_2098_ = lean_nat_add(v___x_2097_, v___x_2095_);
lean_dec(v___x_2097_);
v___x_2099_ = l_Lean_Syntax_Traverser_down(v___x_2093_, v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2100_){
_start:
{
lean_object* v_cur_2101_; 
v_cur_2101_ = lean_ctor_get(v_self_2100_, 0);
lean_inc(v_cur_2101_);
return v_cur_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2102_);
lean_dec_ref(v_self_2102_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2105_, lean_object* v_t_2106_){
_start:
{
lean_object* v_toApplicative_2107_; lean_object* v_toFunctor_2108_; lean_object* v_map_2109_; lean_object* v_get_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; 
v_toApplicative_2107_ = lean_ctor_get(v_inst_2105_, 0);
lean_inc_ref(v_toApplicative_2107_);
lean_dec_ref(v_inst_2105_);
v_toFunctor_2108_ = lean_ctor_get(v_toApplicative_2107_, 0);
lean_inc_ref(v_toFunctor_2108_);
lean_dec_ref(v_toApplicative_2107_);
v_map_2109_ = lean_ctor_get(v_toFunctor_2108_, 0);
lean_inc(v_map_2109_);
lean_dec_ref(v_toFunctor_2108_);
v_get_2110_ = lean_ctor_get(v_t_2106_, 0);
lean_inc(v_get_2110_);
lean_dec_ref(v_t_2106_);
v___f_2111_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2112_ = lean_apply_4(v_map_2109_, lean_box(0), lean_box(0), v___f_2111_, v_get_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2113_, lean_object* v_inst_2114_, lean_object* v_t_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2114_, v_t_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2117_, lean_object* v_s_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = l_Lean_Syntax_Traverser_setCur(v_s_2118_, v_stx_2117_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2122_, lean_object* v_stx_2123_){
_start:
{
lean_object* v_modifyGet_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; 
v_modifyGet_2124_ = lean_ctor_get(v_t_2122_, 2);
lean_inc(v_modifyGet_2124_);
lean_dec_ref(v_t_2122_);
v___f_2125_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2125_, 0, v_stx_2123_);
v___x_2126_ = lean_apply_2(v_modifyGet_2124_, lean_box(0), v___f_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2127_, lean_object* v_t_2128_, lean_object* v_stx_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2128_, v_stx_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2131_, lean_object* v_s_2132_){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = l_Lean_Syntax_Traverser_down(v_s_2132_, v_idx_2131_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2136_, lean_object* v_idx_2137_){
_start:
{
lean_object* v_modifyGet_2138_; lean_object* v___f_2139_; lean_object* v___x_2140_; 
v_modifyGet_2138_ = lean_ctor_get(v_t_2136_, 2);
lean_inc(v_modifyGet_2138_);
lean_dec_ref(v_t_2136_);
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2139_, 0, v_idx_2137_);
v___x_2140_ = lean_apply_2(v_modifyGet_2138_, lean_box(0), v___f_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2141_, lean_object* v_t_2142_, lean_object* v_idx_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2142_, v_idx_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = l_Lean_Syntax_Traverser_up(v_s_2145_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2150_){
_start:
{
lean_object* v_modifyGet_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; 
v_modifyGet_2151_ = lean_ctor_get(v_t_2150_, 2);
lean_inc(v_modifyGet_2151_);
lean_dec_ref(v_t_2150_);
v___f_2152_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2153_ = lean_apply_2(v_modifyGet_2151_, lean_box(0), v___f_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2154_, lean_object* v_t_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_box(0);
v___x_2159_ = l_Lean_Syntax_Traverser_left(v_s_2157_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2162_){
_start:
{
lean_object* v_modifyGet_2163_; lean_object* v___f_2164_; lean_object* v___x_2165_; 
v_modifyGet_2163_ = lean_ctor_get(v_t_2162_, 2);
lean_inc(v_modifyGet_2163_);
lean_dec_ref(v_t_2162_);
v___f_2164_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2165_ = lean_apply_2(v_modifyGet_2163_, lean_box(0), v___f_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2166_, lean_object* v_t_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_box(0);
v___x_2171_ = l_Lean_Syntax_Traverser_right(v_s_2169_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2174_){
_start:
{
lean_object* v_modifyGet_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; 
v_modifyGet_2175_ = lean_ctor_get(v_t_2174_, 2);
lean_inc(v_modifyGet_2175_);
lean_dec_ref(v_t_2174_);
v___f_2176_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2177_ = lean_apply_2(v_modifyGet_2175_, lean_box(0), v___f_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2178_, lean_object* v_t_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2181_, lean_object* v_st_2182_){
_start:
{
lean_object* v_idxs_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_idxs_2183_ = lean_ctor_get(v_st_2182_, 2);
v___x_2184_ = lean_array_get_size(v_idxs_2183_);
v___x_2185_ = lean_unsigned_to_nat(1u);
v___x_2186_ = lean_nat_sub(v___x_2184_, v___x_2185_);
v___x_2187_ = lean_nat_dec_lt(v___x_2186_, v___x_2184_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v___x_2186_);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_apply_2(v_toPure_2181_, lean_box(0), v___x_2188_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_array_fget_borrowed(v_idxs_2183_, v___x_2186_);
lean_dec(v___x_2186_);
lean_inc(v___x_2190_);
v___x_2191_ = lean_apply_2(v_toPure_2181_, lean_box(0), v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2192_, lean_object* v_st_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2192_, v_st_2193_);
lean_dec_ref(v_st_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2195_, lean_object* v_t_2196_){
_start:
{
lean_object* v_toApplicative_2197_; lean_object* v_toBind_2198_; lean_object* v_get_2199_; lean_object* v_toPure_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; 
v_toApplicative_2197_ = lean_ctor_get(v_inst_2195_, 0);
lean_inc_ref(v_toApplicative_2197_);
v_toBind_2198_ = lean_ctor_get(v_inst_2195_, 1);
lean_inc(v_toBind_2198_);
lean_dec_ref(v_inst_2195_);
v_get_2199_ = lean_ctor_get(v_t_2196_, 0);
lean_inc(v_get_2199_);
lean_dec_ref(v_t_2196_);
v_toPure_2200_ = lean_ctor_get(v_toApplicative_2197_, 1);
lean_inc(v_toPure_2200_);
lean_dec_ref(v_toApplicative_2197_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2201_, 0, v_toPure_2200_);
v___x_2202_ = lean_apply_4(v_toBind_2198_, lean_box(0), lean_box(0), v_get_2199_, v___f_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2203_, lean_object* v_inst_2204_, lean_object* v_t_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2204_, v_t_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2207_, lean_object* v_i_2208_){
_start:
{
lean_object* v_args_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_args_2209_ = lean_ctor_get(v_n_2207_, 2);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_array_get_borrowed(v___x_2210_, v_args_2209_, v_i_2208_);
v___x_2212_ = l_Lean_Syntax_getId(v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2213_, lean_object* v_i_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_SyntaxNode_getIdAt(v_n_2213_, v_i_2214_);
lean_dec(v_i_2214_);
lean_dec(v_n_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2216_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2218_ = lean_box(2);
v___x_2219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2217_);
lean_ctor_set(v___x_2219_, 2, v_args_2216_);
return v___x_2219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2225_) == 1)
{
lean_object* v_kind_2226_; 
v_kind_2226_ = lean_ctor_get(v_x_2225_, 1);
if (lean_obj_tag(v_kind_2226_) == 1)
{
lean_object* v_pre_2227_; lean_object* v_str_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_pre_2227_ = lean_ctor_get(v_kind_2226_, 0);
v_str_2228_ = lean_ctor_get(v_kind_2226_, 1);
v___x_2229_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2230_ = lean_string_dec_eq(v_str_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2232_ = lean_string_dec_eq(v_str_2228_, v___x_2231_);
if (v___x_2232_ == 0)
{
return v___x_2232_;
}
else
{
if (lean_obj_tag(v_pre_2227_) == 1)
{
lean_object* v_pre_2233_; 
v_pre_2233_ = lean_ctor_get(v_pre_2227_, 0);
if (lean_obj_tag(v_pre_2233_) == 1)
{
lean_object* v_pre_2234_; 
v_pre_2234_ = lean_ctor_get(v_pre_2233_, 0);
if (lean_obj_tag(v_pre_2234_) == 1)
{
lean_object* v_pre_2235_; 
v_pre_2235_ = lean_ctor_get(v_pre_2234_, 0);
if (lean_obj_tag(v_pre_2235_) == 0)
{
lean_object* v_str_2236_; lean_object* v_str_2237_; lean_object* v_str_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_str_2236_ = lean_ctor_get(v_pre_2227_, 1);
v_str_2237_ = lean_ctor_get(v_pre_2233_, 1);
v_str_2238_ = lean_ctor_get(v_pre_2234_, 1);
v___x_2239_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2240_ = lean_string_dec_eq(v_str_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
return v___x_2230_;
}
else
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2242_ = lean_string_dec_eq(v_str_2237_, v___x_2241_);
if (v___x_2242_ == 0)
{
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2244_ = lean_string_dec_eq(v_str_2236_, v___x_2243_);
return v___x_2244_;
}
}
}
else
{
return v___x_2230_;
}
}
else
{
return v___x_2230_;
}
}
else
{
return v___x_2230_;
}
}
else
{
return v___x_2230_;
}
}
}
else
{
return v___x_2230_;
}
}
else
{
uint8_t v___x_2245_; 
v___x_2245_ = 0;
return v___x_2245_;
}
}
else
{
uint8_t v___x_2246_; 
v___x_2246_ = 0;
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2247_){
_start:
{
uint8_t v_res_2248_; lean_object* v_r_2249_; 
v_res_2248_ = l_Lean_Syntax_isQuot(v_x_2247_);
lean_dec(v_x_2247_);
v_r_2249_ = lean_box(v_res_2248_);
return v_r_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2255_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___y_2259_; uint8_t v___x_2265_; 
v___x_2256_ = l_Lean_Syntax_getNumArgs(v_stx_2255_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_dec_eq(v___x_2256_, v___x_2257_);
lean_dec(v___x_2256_);
if (v___x_2265_ == 0)
{
v___y_2259_ = v_stx_2255_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = l_Lean_Syntax_getArg(v_stx_2255_, v___x_2266_);
lean_dec(v_stx_2255_);
v___y_2259_ = v___x_2267_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2259_);
v___x_2261_ = l_Lean_Syntax_isOfKind(v___y_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Syntax_getArg(v___y_2259_, v___x_2257_);
lean_dec(v___y_2259_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_unsigned_to_nat(3u);
v___x_2264_ = l_Lean_Syntax_getArg(v___y_2259_, v___x_2263_);
lean_dec(v___y_2259_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2269_){
_start:
{
if (lean_obj_tag(v_x_2269_) == 1)
{
lean_object* v_kind_2270_; 
v_kind_2270_ = lean_ctor_get(v_x_2269_, 1);
if (lean_obj_tag(v_kind_2270_) == 1)
{
lean_object* v_str_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_str_2271_ = lean_ctor_get(v_kind_2270_, 1);
v___x_2272_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2273_ = lean_string_dec_eq(v_str_2271_, v___x_2272_);
return v___x_2273_;
}
else
{
uint8_t v___x_2274_; 
v___x_2274_ = 0;
return v___x_2274_;
}
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = 0;
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2276_){
_start:
{
uint8_t v_res_2277_; lean_object* v_r_2278_; 
v_res_2277_ = l_Lean_Syntax_isAntiquot(v_x_2276_);
lean_dec(v_x_2276_);
v_r_2278_ = lean_box(v_res_2277_);
return v_r_2278_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2279_, uint8_t v___x_2280_, lean_object* v_as_2281_, size_t v_i_2282_, size_t v_stop_2283_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = lean_usize_dec_eq(v_i_2282_, v_stop_2283_);
if (v___x_2284_ == 0)
{
uint8_t v___x_2285_; uint8_t v___y_2287_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2285_ = 1;
v___x_2291_ = lean_array_uget_borrowed(v_as_2281_, v_i_2282_);
v___x_2292_ = l_Lean_Syntax_isAntiquot(v___x_2291_);
if (v___x_2292_ == 0)
{
v___y_2287_ = v___y_2279_;
goto v___jp_2286_;
}
else
{
v___y_2287_ = v___x_2280_;
goto v___jp_2286_;
}
v___jp_2286_:
{
if (v___y_2287_ == 0)
{
size_t v___x_2288_; size_t v___x_2289_; 
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_add(v_i_2282_, v___x_2288_);
v_i_2282_ = v___x_2289_;
goto _start;
}
else
{
return v___x_2285_;
}
}
}
else
{
uint8_t v___x_2293_; 
v___x_2293_ = 0;
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2294_, lean_object* v___x_2295_, lean_object* v_as_2296_, lean_object* v_i_2297_, lean_object* v_stop_2298_){
_start:
{
uint8_t v___y_330__boxed_2299_; uint8_t v___x_331__boxed_2300_; size_t v_i_boxed_2301_; size_t v_stop_boxed_2302_; uint8_t v_res_2303_; lean_object* v_r_2304_; 
v___y_330__boxed_2299_ = lean_unbox(v___y_2294_);
v___x_331__boxed_2300_ = lean_unbox(v___x_2295_);
v_i_boxed_2301_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_stop_boxed_2302_ = lean_unbox_usize(v_stop_2298_);
lean_dec(v_stop_2298_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_330__boxed_2299_, v___x_331__boxed_2300_, v_as_2296_, v_i_boxed_2301_, v_stop_boxed_2302_);
lean_dec_ref(v_as_2296_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2305_){
_start:
{
uint8_t v___x_2306_; uint8_t v___y_2308_; 
v___x_2306_ = l_Lean_Syntax_isAntiquot(v_stx_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2305_);
v___x_2317_ = l_Lean_Syntax_isOfKind(v_stx_2305_, v___x_2316_);
if (v___x_2317_ == 0)
{
v___y_2308_ = v___x_2317_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = l_Lean_Syntax_getNumArgs(v_stx_2305_);
v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
lean_dec(v___x_2319_);
v___y_2308_ = v___x_2320_;
goto v___jp_2307_;
}
}
else
{
lean_dec(v_stx_2305_);
return v___x_2306_;
}
v___jp_2307_:
{
if (v___y_2308_ == 0)
{
lean_dec(v_stx_2305_);
return v___y_2308_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2309_ = l_Lean_Syntax_getArgs(v_stx_2305_);
lean_dec(v_stx_2305_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = lean_array_get_size(v___x_2309_);
v___x_2312_ = lean_nat_dec_lt(v___x_2310_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2309_);
return v___y_2308_;
}
else
{
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2309_);
return v___y_2308_;
}
else
{
size_t v___x_2313_; size_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2313_ = ((size_t)0ULL);
v___x_2314_ = lean_usize_of_nat(v___x_2311_);
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2308_, v___x_2306_, v___x_2309_, v___x_2313_, v___x_2314_);
lean_dec_ref(v___x_2309_);
if (v___x_2315_ == 0)
{
return v___x_2312_;
}
else
{
return v___x_2306_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2321_){
_start:
{
uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_res_2322_ = l_Lean_Syntax_isAntiquots(v_stx_2321_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2324_){
_start:
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2324_);
v___x_2326_ = l_Lean_Syntax_isOfKind(v_stx_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
return v_stx_2324_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = l_Lean_Syntax_getArg(v_stx_2324_, v___x_2327_);
lean_dec(v_stx_2324_);
return v___x_2328_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2331_ = l_Lean_mkAtom(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2335_ = lean_unsigned_to_nat(4u);
v___x_2336_ = lean_mk_empty_array_with_capacity(v___x_2335_);
v___x_2337_ = lean_array_push(v___x_2336_, v___x_2334_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2346_ = l_Lean_mkAtom(v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2348_ = lean_unsigned_to_nat(2u);
v___x_2349_ = lean_mk_empty_array_with_capacity(v___x_2348_);
v___x_2350_ = lean_array_push(v___x_2349_, v___x_2347_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2362_ = l_Lean_mkAtom(v___x_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2365_ = l_Lean_mkAtom(v___x_2364_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2366_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2367_ = lean_unsigned_to_nat(3u);
v___x_2368_ = lean_mk_empty_array_with_capacity(v___x_2367_);
v___x_2369_ = lean_array_push(v___x_2368_, v___x_2366_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2370_, lean_object* v_term_2371_, lean_object* v_nesting_2372_, lean_object* v_name_2373_, uint8_t v_isPseudoKind_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_nesting_2379_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2398_; uint8_t v___x_2406_; 
v___x_2375_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2376_ = lean_mk_array(v_nesting_2372_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2378_ = lean_box(2);
v_nesting_2379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2379_, 0, v___x_2378_);
lean_ctor_set(v_nesting_2379_, 1, v___x_2377_);
lean_ctor_set(v_nesting_2379_, 2, v___x_2376_);
v___x_2406_ = l_Lean_Syntax_isIdent(v_term_2371_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2371_);
v___x_2408_ = l_Lean_Syntax_isOfKind(v_term_2371_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2409_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2410_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2411_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2412_ = lean_array_push(v___x_2411_, v_term_2371_);
v___x_2413_ = lean_array_push(v___x_2412_, v___x_2410_);
v___x_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2378_);
lean_ctor_set(v___x_2414_, 1, v___x_2409_);
lean_ctor_set(v___x_2414_, 2, v___x_2413_);
v___y_2398_ = v___x_2414_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = l_Lean_Syntax_getArg(v_term_2371_, v___x_2415_);
lean_dec(v_term_2371_);
v___y_2398_ = v___x_2416_;
goto v___jp_2397_;
}
}
else
{
v___y_2398_ = v_term_2371_;
goto v___jp_2397_;
}
v___jp_2380_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_inc(v___y_2383_);
v___x_2384_ = l_Lean_Name_append(v_kind_2370_, v___y_2383_);
v___x_2385_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2386_ = l_Lean_Name_append(v___x_2384_, v___x_2385_);
v___x_2387_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2388_ = lean_array_push(v___x_2387_, v_nesting_2379_);
v___x_2389_ = lean_array_push(v___x_2388_, v___y_2381_);
v___x_2390_ = lean_array_push(v___x_2389_, v___y_2382_);
v___x_2391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2378_);
lean_ctor_set(v___x_2391_, 1, v___x_2386_);
lean_ctor_set(v___x_2391_, 2, v___x_2390_);
return v___x_2391_;
}
v___jp_2392_:
{
if (v_isPseudoKind_2374_ == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_box(0);
v___y_2381_ = v___y_2393_;
v___y_2382_ = v___y_2394_;
v___y_2383_ = v___x_2395_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2396_; 
v___x_2396_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2381_ = v___y_2393_;
v___y_2382_ = v___y_2394_;
v___y_2383_ = v___x_2396_;
goto v___jp_2380_;
}
}
v___jp_2397_:
{
if (lean_obj_tag(v_name_2373_) == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2393_ = v___y_2398_;
v___y_2394_ = v___x_2399_;
goto v___jp_2392_;
}
else
{
lean_object* v_val_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_val_2400_ = lean_ctor_get(v_name_2373_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v_name_2373_, 1);
v___x_2401_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2402_ = l_Lean_mkAtom(v_val_2400_);
v___x_2403_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2404_ = lean_array_push(v___x_2403_, v___x_2402_);
v___x_2405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2378_);
lean_ctor_set(v___x_2405_, 1, v___x_2401_);
lean_ctor_set(v___x_2405_, 2, v___x_2404_);
v___y_2393_ = v___y_2398_;
v___y_2394_ = v___x_2405_;
goto v___jp_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2417_, lean_object* v_term_2418_, lean_object* v_nesting_2419_, lean_object* v_name_2420_, lean_object* v_isPseudoKind_2421_){
_start:
{
uint8_t v_isPseudoKind_boxed_2422_; lean_object* v_res_2423_; 
v_isPseudoKind_boxed_2422_ = lean_unbox(v_isPseudoKind_2421_);
v_res_2423_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2417_, v_term_2418_, v_nesting_2419_, v_name_2420_, v_isPseudoKind_boxed_2422_);
return v_res_2423_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = l_Lean_Syntax_getArg(v_stx_2424_, v___x_2425_);
v___x_2427_ = l_Lean_Syntax_getArgs(v___x_2426_);
lean_dec(v___x_2426_);
v___x_2428_ = lean_array_get_size(v___x_2427_);
lean_dec_ref(v___x_2427_);
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = lean_nat_dec_eq(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
uint8_t v___x_2431_; 
v___x_2431_ = 1;
return v___x_2431_;
}
else
{
uint8_t v___x_2432_; 
v___x_2432_ = 0;
return v___x_2432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2433_);
lean_dec(v_stx_2433_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = l_Lean_Syntax_isAntiquot(v_stx_2436_);
if (v___x_2437_ == 0)
{
return v_stx_2436_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = l_Lean_Syntax_getArg(v_stx_2436_, v___x_2438_);
v___x_2440_ = l_Lean_Syntax_getArgs(v___x_2439_);
lean_dec(v___x_2439_);
v___x_2441_ = lean_array_pop(v___x_2440_);
v___x_2442_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2443_ = lean_box(2);
v___x_2444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v___x_2442_);
lean_ctor_set(v___x_2444_, 2, v___x_2441_);
v___x_2445_ = l_Lean_Syntax_setArg(v_stx_2436_, v___x_2438_, v___x_2444_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2446_){
_start:
{
lean_object* v___y_2448_; uint8_t v___x_2459_; 
v___x_2459_ = l_Lean_Syntax_isAntiquot(v_stx_2446_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_unsigned_to_nat(3u);
v___x_2461_ = l_Lean_Syntax_getArg(v_stx_2446_, v___x_2460_);
v___y_2448_ = v___x_2461_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_unsigned_to_nat(2u);
v___x_2463_ = l_Lean_Syntax_getArg(v_stx_2446_, v___x_2462_);
v___y_2448_ = v___x_2463_;
goto v___jp_2447_;
}
v___jp_2447_:
{
uint8_t v___x_2449_; 
v___x_2449_ = l_Lean_Syntax_isIdent(v___y_2448_);
if (v___x_2449_ == 0)
{
uint8_t v___x_2450_; 
v___x_2450_ = l_Lean_Syntax_isAtom(v___y_2448_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = l_Lean_Syntax_getArg(v___y_2448_, v___x_2451_);
lean_dec(v___y_2448_);
return v___x_2452_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2453_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_mk_empty_array_with_capacity(v___x_2454_);
v___x_2456_ = lean_array_push(v___x_2455_, v___y_2448_);
v___x_2457_ = lean_box(2);
v___x_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___x_2453_);
lean_ctor_set(v___x_2458_, 2, v___x_2456_);
return v___x_2458_;
}
}
else
{
return v___y_2448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2464_);
lean_dec(v_stx_2464_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2466_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 1)
{
lean_object* v_kind_2467_; 
v_kind_2467_ = lean_ctor_get(v_x_2466_, 1);
if (lean_obj_tag(v_kind_2467_) == 1)
{
lean_object* v_pre_2468_; lean_object* v_str_2469_; 
v_pre_2468_ = lean_ctor_get(v_kind_2467_, 0);
v_str_2469_ = lean_ctor_get(v_kind_2467_, 1);
if (lean_obj_tag(v_pre_2468_) == 1)
{
lean_object* v_pre_2475_; lean_object* v_str_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v_pre_2475_ = lean_ctor_get(v_pre_2468_, 0);
v_str_2476_ = lean_ctor_get(v_pre_2468_, 1);
v___x_2477_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2478_ = lean_string_dec_eq(v_str_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2480_ = lean_string_dec_eq(v_str_2469_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_box(0);
return v___x_2481_;
}
else
{
goto v___jp_2470_;
}
}
else
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2483_ = lean_string_dec_eq(v_str_2469_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = lean_box(v___x_2483_);
lean_inc(v_pre_2475_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_pre_2475_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
}
else
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2489_ = lean_string_dec_eq(v_str_2469_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_box(0);
return v___x_2490_;
}
else
{
goto v___jp_2470_;
}
}
v___jp_2470_:
{
uint8_t v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2471_ = 0;
v___x_2472_ = lean_box(v___x_2471_);
lean_inc(v_pre_2468_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_pre_2468_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
return v___x_2474_;
}
}
else
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
}
else
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_box(0);
return v___x_2492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2493_);
lean_dec(v_x_2493_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2495_, size_t v_i_2496_, size_t v_stop_2497_, lean_object* v_b_2498_){
_start:
{
lean_object* v___y_2500_; uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_eq(v_i_2496_, v_stop_2497_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_array_uget_borrowed(v_as_2495_, v_i_2496_);
v___x_2506_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2505_);
if (lean_obj_tag(v___x_2506_) == 0)
{
v___y_2500_ = v_b_2498_;
goto v___jp_2499_;
}
else
{
lean_object* v_val_2507_; lean_object* v___x_2508_; 
v_val_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_val_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = lean_array_push(v_b_2498_, v_val_2507_);
v___y_2500_ = v___x_2508_;
goto v___jp_2499_;
}
}
else
{
return v_b_2498_;
}
v___jp_2499_:
{
size_t v___x_2501_; size_t v___x_2502_; 
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_add(v_i_2496_, v___x_2501_);
v_i_2496_ = v___x_2502_;
v_b_2498_ = v___y_2500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2509_, lean_object* v_i_2510_, lean_object* v_stop_2511_, lean_object* v_b_2512_){
_start:
{
size_t v_i_boxed_2513_; size_t v_stop_boxed_2514_; lean_object* v_res_2515_; 
v_i_boxed_2513_ = lean_unbox_usize(v_i_2510_);
lean_dec(v_i_2510_);
v_stop_boxed_2514_ = lean_unbox_usize(v_stop_2511_);
lean_dec(v_stop_2511_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2509_, v_i_boxed_2513_, v_stop_boxed_2514_, v_b_2512_);
lean_dec_ref(v_as_2509_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2518_, lean_object* v_start_2519_, lean_object* v_stop_2520_){
_start:
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2522_ = lean_nat_dec_lt(v_start_2519_, v_stop_2520_);
if (v___x_2522_ == 0)
{
return v___x_2521_;
}
else
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = lean_array_get_size(v_as_2518_);
v___x_2524_ = lean_nat_dec_le(v_stop_2520_, v___x_2523_);
if (v___x_2524_ == 0)
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_nat_dec_lt(v_start_2519_, v___x_2523_);
if (v___x_2525_ == 0)
{
return v___x_2521_;
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_usize_of_nat(v_start_2519_);
v___x_2527_ = lean_usize_of_nat(v___x_2523_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2518_, v___x_2526_, v___x_2527_, v___x_2521_);
return v___x_2528_;
}
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_usize_of_nat(v_start_2519_);
v___x_2530_ = lean_usize_of_nat(v_stop_2520_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2518_, v___x_2529_, v___x_2530_, v___x_2521_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2532_, lean_object* v_start_2533_, lean_object* v_stop_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2532_, v_start_2533_, v_stop_2534_);
lean_dec(v_stop_2534_);
lean_dec(v_start_2533_);
lean_dec_ref(v_as_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2536_){
_start:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2536_);
v___x_2538_ = l_Lean_Syntax_isOfKind(v_stx_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2536_);
lean_dec(v_stx_2536_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_box(0);
return v___x_2540_;
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v_val_2541_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_val_2541_);
lean_dec_ref_known(v___x_2539_, 1);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_val_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
return v___x_2543_;
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2544_ = l_Lean_Syntax_getArgs(v_stx_2536_);
lean_dec(v_stx_2536_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v___x_2544_);
v___x_2547_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2544_, v___x_2545_, v___x_2546_);
lean_dec_ref(v___x_2544_);
v___x_2548_ = lean_array_to_list(v___x_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2550_) == 1)
{
lean_object* v_kind_2551_; 
v_kind_2551_ = lean_ctor_get(v_x_2550_, 1);
if (lean_obj_tag(v_kind_2551_) == 1)
{
lean_object* v_pre_2552_; lean_object* v_str_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v_pre_2552_ = lean_ctor_get(v_kind_2551_, 0);
v_str_2553_ = lean_ctor_get(v_kind_2551_, 1);
v___x_2554_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2555_ = lean_string_dec_eq(v_str_2553_, v___x_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_box(0);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; 
lean_inc(v_pre_2552_);
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_pre_2552_);
return v___x_2557_;
}
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
}
else
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_box(0);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2560_);
lean_dec(v_x_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2562_);
if (lean_obj_tag(v___x_2563_) == 0)
{
uint8_t v___x_2564_; 
v___x_2564_ = 0;
return v___x_2564_;
}
else
{
uint8_t v___x_2565_; 
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = 1;
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2566_){
_start:
{
uint8_t v_res_2567_; lean_object* v_r_2568_; 
v_res_2567_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2566_);
lean_dec(v_stx_2566_);
v_r_2568_ = lean_box(v_res_2567_);
return v_r_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_unsigned_to_nat(3u);
v___x_2571_ = l_Lean_Syntax_getArg(v_stx_2569_, v___x_2570_);
v___x_2572_ = l_Lean_Syntax_getArgs(v___x_2571_);
lean_dec(v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2573_);
lean_dec(v_stx_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2575_){
_start:
{
uint8_t v___x_2576_; 
v___x_2576_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_unsigned_to_nat(1u);
v___x_2578_ = l_Lean_Syntax_getArg(v_stx_2575_, v___x_2577_);
return v___x_2578_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_unsigned_to_nat(5u);
v___x_2580_ = l_Lean_Syntax_getArg(v_stx_2575_, v___x_2579_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2581_);
lean_dec(v_stx_2581_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2588_ = l_Lean_mkAtom(v___x_2587_);
return v___x_2588_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2591_ = l_Lean_mkAtom(v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2592_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2593_ = lean_unsigned_to_nat(6u);
v___x_2594_ = lean_mk_empty_array_with_capacity(v___x_2593_);
v___x_2595_ = lean_array_push(v___x_2594_, v___x_2592_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2596_, lean_object* v_contents_2597_, lean_object* v_suffix_2598_, lean_object* v_nesting_2599_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v_nesting_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2600_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2601_ = lean_mk_array(v_nesting_2599_, v___x_2600_);
v___x_2602_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2603_ = lean_box(2);
v_nesting_2604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2604_, 0, v___x_2603_);
lean_ctor_set(v_nesting_2604_, 1, v___x_2602_);
lean_ctor_set(v_nesting_2604_, 2, v___x_2601_);
v___x_2605_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2606_ = l_Lean_Name_append(v_kind_2596_, v___x_2605_);
v___x_2607_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2603_);
lean_ctor_set(v___x_2608_, 1, v___x_2602_);
lean_ctor_set(v___x_2608_, 2, v_contents_2597_);
v___x_2609_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2610_ = l_Lean_mkAtom(v_suffix_2598_);
v___x_2611_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2612_ = lean_array_push(v___x_2611_, v_nesting_2604_);
v___x_2613_ = lean_array_push(v___x_2612_, v___x_2607_);
v___x_2614_ = lean_array_push(v___x_2613_, v___x_2608_);
v___x_2615_ = lean_array_push(v___x_2614_, v___x_2609_);
v___x_2616_ = lean_array_push(v___x_2615_, v___x_2610_);
v___x_2617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2603_);
lean_ctor_set(v___x_2617_, 1, v___x_2606_);
lean_ctor_set(v___x_2617_, 2, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2619_){
_start:
{
if (lean_obj_tag(v_x_2619_) == 1)
{
lean_object* v_kind_2620_; 
v_kind_2620_ = lean_ctor_get(v_x_2619_, 1);
if (lean_obj_tag(v_kind_2620_) == 1)
{
lean_object* v_pre_2621_; lean_object* v_str_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v_pre_2621_ = lean_ctor_get(v_kind_2620_, 0);
v_str_2622_ = lean_ctor_get(v_kind_2620_, 1);
v___x_2623_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2624_ = lean_string_dec_eq(v_str_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_box(0);
return v___x_2625_;
}
else
{
lean_object* v___x_2626_; 
lean_inc(v_pre_2621_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_pre_2621_);
return v___x_2626_;
}
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_box(0);
return v___x_2627_;
}
}
else
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_box(0);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2629_);
lean_dec(v_x_2629_);
return v_res_2630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
uint8_t v___x_2633_; 
v___x_2633_ = 0;
return v___x_2633_;
}
else
{
uint8_t v___x_2634_; 
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = 1;
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2635_){
_start:
{
uint8_t v_res_2636_; lean_object* v_r_2637_; 
v_res_2636_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2635_);
lean_dec(v_stx_2635_);
v_r_2637_ = lean_box(v_res_2636_);
return v_r_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2638_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = l_Lean_Syntax_getArg(v_stx_2638_, v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2641_);
lean_dec(v_stx_2641_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2645_, lean_object* v_inner_2646_, lean_object* v_suffix_2647_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2648_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2649_ = l_Lean_Name_append(v_kind_2645_, v___x_2648_);
v___x_2650_ = l_Lean_mkAtom(v_suffix_2647_);
v___x_2651_ = lean_unsigned_to_nat(2u);
v___x_2652_ = lean_mk_empty_array_with_capacity(v___x_2651_);
v___x_2653_ = lean_array_push(v___x_2652_, v_inner_2646_);
v___x_2654_ = lean_array_push(v___x_2653_, v___x_2650_);
v___x_2655_ = lean_box(2);
v___x_2656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v___x_2649_);
lean_ctor_set(v___x_2656_, 2, v___x_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2660_){
_start:
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2662_ = l_Lean_Syntax_isOfKind(v_stx_2660_, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2663_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2666_){
_start:
{
uint8_t v___y_2668_; uint8_t v___x_2671_; 
v___x_2671_ = l_Lean_Syntax_isAntiquot(v_stx_2666_);
if (v___x_2671_ == 0)
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2666_);
v___y_2668_ = v___x_2672_;
goto v___jp_2667_;
}
else
{
v___y_2668_ = v___x_2671_;
goto v___jp_2667_;
}
v___jp_2667_:
{
if (v___y_2668_ == 0)
{
uint8_t v___x_2669_; 
v___x_2669_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2666_);
if (v___x_2669_ == 0)
{
uint8_t v___x_2670_; 
v___x_2670_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2666_);
return v___x_2670_;
}
else
{
lean_dec(v_stx_2666_);
return v___x_2669_;
}
}
else
{
lean_dec(v_stx_2666_);
return v___y_2668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2673_){
_start:
{
uint8_t v_res_2674_; lean_object* v_r_2675_; 
v_res_2674_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2673_);
v_r_2675_ = lean_box(v_res_2674_);
return v_r_2675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2679_, lean_object* v_stx_2680_, lean_object* v_visit_2681_, lean_object* v_stack_2682_, lean_object* v_accept_2683_, lean_object* v_a_2684_, lean_object* v_b_2685_){
_start:
{
lean_object* v_a_2687_; uint8_t v___x_2691_; 
v___x_2691_ = lean_nat_dec_lt(v_a_2684_, v_upperBound_2679_);
if (v___x_2691_ == 0)
{
lean_dec(v_a_2684_);
lean_dec_ref(v_accept_2683_);
lean_dec(v_stack_2682_);
lean_dec_ref(v_visit_2681_);
lean_dec(v_stx_2680_);
lean_inc_ref(v_b_2685_);
return v_b_2685_;
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2694_ = l_Lean_Syntax_getArg(v_stx_2680_, v_a_2684_);
lean_inc_ref(v_visit_2681_);
lean_inc(v___x_2694_);
v___x_2695_ = lean_apply_1(v_visit_2681_, v___x_2694_);
v___x_2696_ = lean_unbox(v___x_2695_);
if (v___x_2696_ == 0)
{
lean_dec(v___x_2694_);
v_a_2687_ = v___x_2693_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_inc(v_a_2684_);
lean_inc(v_stx_2680_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_stx_2680_);
lean_ctor_set(v___x_2697_, 1, v_a_2684_);
lean_inc(v_stack_2682_);
v___x_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_stack_2682_);
lean_inc_ref(v_accept_2683_);
lean_inc_ref(v_visit_2681_);
v___x_2699_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2681_, v_accept_2683_, v___x_2698_, v___x_2694_);
if (lean_obj_tag(v___x_2699_) == 1)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec(v_a_2684_);
lean_dec_ref(v_accept_2683_);
lean_dec(v_stack_2682_);
lean_dec_ref(v_visit_2681_);
lean_dec(v_stx_2680_);
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v___x_2692_);
return v___x_2701_;
}
else
{
lean_dec(v___x_2699_);
v_a_2687_ = v___x_2693_;
goto v___jp_2686_;
}
}
}
v___jp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_nat_add(v_a_2684_, v___x_2688_);
lean_dec(v_a_2684_);
v_a_2684_ = v___x_2689_;
v_b_2685_ = v_a_2687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2702_, lean_object* v_accept_2703_, lean_object* v_stack_2704_, lean_object* v_stx_2705_){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
lean_inc_ref(v_accept_2703_);
lean_inc(v_stx_2705_);
v___x_2706_ = lean_apply_1(v_accept_2703_, v_stx_2705_);
v___x_2707_ = lean_unbox(v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v_fst_2713_; 
v___x_2708_ = l_Lean_Syntax_getNumArgs(v_stx_2705_);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_box(0);
v___x_2711_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2708_, v_stx_2705_, v_visit_2702_, v_stack_2704_, v_accept_2703_, v___x_2709_, v___x_2711_);
lean_dec(v___x_2708_);
v_fst_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_fst_2713_);
lean_dec_ref(v___x_2712_);
if (lean_obj_tag(v_fst_2713_) == 0)
{
return v___x_2710_;
}
else
{
lean_object* v_val_2714_; 
v_val_2714_ = lean_ctor_get(v_fst_2713_, 0);
lean_inc(v_val_2714_);
lean_dec_ref_known(v_fst_2713_, 1);
return v_val_2714_;
}
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v_accept_2703_);
lean_dec_ref(v_visit_2702_);
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_stx_2705_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v_stack_2704_);
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2719_, lean_object* v_stx_2720_, lean_object* v_visit_2721_, lean_object* v_stack_2722_, lean_object* v_accept_2723_, lean_object* v_a_2724_, lean_object* v_b_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2719_, v_stx_2720_, v_visit_2721_, v_stack_2722_, v_accept_2723_, v_a_2724_, v_b_2725_);
lean_dec_ref(v_b_2725_);
lean_dec(v_upperBound_2719_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2727_, lean_object* v_stx_2728_, lean_object* v_visit_2729_, lean_object* v_stack_2730_, lean_object* v_accept_2731_, lean_object* v_inst_2732_, lean_object* v_R_2733_, lean_object* v_a_2734_, lean_object* v_b_2735_, lean_object* v_c_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2727_, v_stx_2728_, v_visit_2729_, v_stack_2730_, v_accept_2731_, v_a_2734_, v_b_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2738_, lean_object* v_stx_2739_, lean_object* v_visit_2740_, lean_object* v_stack_2741_, lean_object* v_accept_2742_, lean_object* v_inst_2743_, lean_object* v_R_2744_, lean_object* v_a_2745_, lean_object* v_b_2746_, lean_object* v_c_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2738_, v_stx_2739_, v_visit_2740_, v_stack_2741_, v_accept_2742_, v_inst_2743_, v_R_2744_, v_a_2745_, v_b_2746_, v_c_2747_);
lean_dec_ref(v_b_2746_);
lean_dec(v_upperBound_2738_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2749_, lean_object* v_visit_2750_, lean_object* v_accept_2751_){
_start:
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
lean_inc_ref(v_visit_2750_);
lean_inc(v_root_2749_);
v___x_2752_ = lean_apply_1(v_visit_2750_, v_root_2749_);
v___x_2753_ = lean_unbox(v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
lean_dec_ref(v_accept_2751_);
lean_dec_ref(v_visit_2750_);
lean_dec(v_root_2749_);
v___x_2754_ = lean_box(0);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_box(0);
v___x_2756_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2750_, v_accept_2751_, v___x_2755_, v_root_2749_);
return v___x_2756_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2757_, lean_object* v_x_2758_, lean_object* v_p_2759_){
_start:
{
if (lean_obj_tag(v_p_2759_) == 0)
{
lean_dec_ref(v_x_2758_);
return v___x_2757_;
}
else
{
lean_object* v_fst_2760_; lean_object* v_val_2761_; uint8_t v___x_2762_; 
v_fst_2760_ = lean_ctor_get(v_x_2758_, 0);
lean_inc(v_fst_2760_);
lean_dec_ref(v_x_2758_);
v_val_2761_ = lean_ctor_get(v_p_2759_, 0);
v___x_2762_ = l_Lean_Syntax_isOfKind(v_fst_2760_, v_val_2761_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2763_, lean_object* v_x_2764_, lean_object* v_p_2765_){
_start:
{
uint8_t v___x_123__boxed_2766_; uint8_t v_res_2767_; lean_object* v_r_2768_; 
v___x_123__boxed_2766_ = lean_unbox(v___x_2763_);
v_res_2767_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2766_, v_x_2764_, v_p_2765_);
lean_dec(v_p_2765_);
v_r_2768_ = lean_box(v_res_2767_);
return v_r_2768_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2769_) == 0)
{
uint8_t v___x_2770_; 
v___x_2770_ = 1;
return v___x_2770_;
}
else
{
lean_object* v_head_2771_; uint8_t v___x_2772_; 
v_head_2771_ = lean_ctor_get(v_x_2769_, 0);
v___x_2772_ = lean_unbox(v_head_2771_);
if (v___x_2772_ == 0)
{
uint8_t v___x_2773_; 
v___x_2773_ = lean_unbox(v_head_2771_);
return v___x_2773_;
}
else
{
lean_object* v_tail_2774_; 
v_tail_2774_ = lean_ctor_get(v_x_2769_, 1);
v_x_2769_ = v_tail_2774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2776_){
_start:
{
uint8_t v_res_2777_; lean_object* v_r_2778_; 
v_res_2777_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2776_);
lean_dec(v_x_2776_);
v_r_2778_ = lean_box(v_res_2777_);
return v_r_2778_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2781_, lean_object* v_pattern_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v___x_2783_ = l_List_lengthTR___redArg(v_pattern_2782_);
v___x_2784_ = l_List_lengthTR___redArg(v_stack_2781_);
v___x_2785_ = lean_nat_dec_le(v___x_2783_, v___x_2784_);
lean_dec(v___x_2784_);
lean_dec(v___x_2783_);
if (v___x_2785_ == 0)
{
lean_dec(v_pattern_2782_);
lean_dec(v_stack_2781_);
return v___x_2785_;
}
else
{
lean_object* v___x_2786_; lean_object* v___f_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2786_ = lean_box(v___x_2785_);
v___f_2787_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2787_, 0, v___x_2786_);
v___x_2788_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2789_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2787_, v_stack_2781_, v_pattern_2782_, v___x_2788_);
v___x_2790_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2789_);
lean_dec(v___x_2789_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2791_, lean_object* v_pattern_2792_){
_start:
{
uint8_t v_res_2793_; lean_object* v_r_2794_; 
v_res_2793_ = l_Lean_Syntax_Stack_matches(v_stack_2791_, v_pattern_2792_);
v_r_2794_ = lean_box(v_res_2793_);
return v_r_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2795_, lean_object* v_trailing_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2795_);
if (lean_obj_tag(v___x_2797_) == 1)
{
lean_object* v_val_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2833_; 
v_val_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2833_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_val_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2833_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
if (lean_obj_tag(v_val_2798_) == 0)
{
lean_object* v_trailing_2802_; lean_object* v_leading_2803_; lean_object* v_pos_2804_; lean_object* v_endPos_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2831_; 
v_trailing_2802_ = lean_ctor_get(v_val_2798_, 2);
v_leading_2803_ = lean_ctor_get(v_val_2798_, 0);
v_pos_2804_ = lean_ctor_get(v_val_2798_, 1);
v_endPos_2805_ = lean_ctor_get(v_val_2798_, 3);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_val_2798_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2807_ = v_val_2798_;
v_isShared_2808_ = v_isSharedCheck_2831_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_endPos_2805_);
lean_inc(v_trailing_2802_);
lean_inc(v_pos_2804_);
lean_inc(v_leading_2803_);
lean_dec(v_val_2798_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2831_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_str_2809_; lean_object* v_startPos_2810_; lean_object* v_stopPos_2811_; lean_object* v_startPos_2812_; lean_object* v_stopPos_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2829_; 
v_str_2809_ = lean_ctor_get(v_trailing_2802_, 0);
lean_inc_ref(v_str_2809_);
v_startPos_2810_ = lean_ctor_get(v_trailing_2802_, 1);
lean_inc(v_startPos_2810_);
v_stopPos_2811_ = lean_ctor_get(v_trailing_2802_, 2);
lean_inc(v_stopPos_2811_);
lean_dec_ref(v_trailing_2802_);
v_startPos_2812_ = lean_ctor_get(v_trailing_2796_, 1);
v_stopPos_2813_ = lean_ctor_get(v_trailing_2796_, 2);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_trailing_2796_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; 
v_unused_2830_ = lean_ctor_get(v_trailing_2796_, 0);
lean_dec(v_unused_2830_);
v___x_2815_ = v_trailing_2796_;
v_isShared_2816_ = v_isSharedCheck_2829_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_stopPos_2813_);
lean_inc(v_startPos_2812_);
lean_dec(v_trailing_2796_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2829_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
uint8_t v_decide_2817_; 
v_decide_2817_ = lean_nat_dec_eq(v_stopPos_2811_, v_startPos_2812_);
lean_dec(v_startPos_2812_);
lean_dec(v_stopPos_2811_);
if (v_decide_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_del_object(v___x_2815_);
lean_dec(v_stopPos_2813_);
lean_dec(v_startPos_2810_);
lean_dec_ref(v_str_2809_);
lean_del_object(v___x_2807_);
lean_dec(v_endPos_2805_);
lean_dec(v_pos_2804_);
lean_dec_ref(v_leading_2803_);
lean_del_object(v___x_2800_);
lean_dec(v_stx_2795_);
v___x_2818_ = lean_box(0);
return v___x_2818_;
}
else
{
lean_object* v_trailing_2820_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_startPos_2810_);
lean_ctor_set(v___x_2815_, 0, v_str_2809_);
v_trailing_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_str_2809_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_startPos_2810_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_stopPos_2813_);
v_trailing_2820_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 2, v_trailing_2820_);
v___x_2822_ = v___x_2807_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_leading_2803_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_pos_2804_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_trailing_2820_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_endPos_2805_);
v___x_2822_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = l_Lean_Syntax_setTailInfo(v_stx_2795_, v___x_2822_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2823_);
v___x_2825_ = v___x_2800_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2832_; 
lean_del_object(v___x_2800_);
lean_dec(v_val_2798_);
lean_dec_ref(v_trailing_2796_);
lean_dec(v_stx_2795_);
v___x_2832_ = lean_box(0);
return v___x_2832_;
}
}
}
else
{
lean_object* v___x_2834_; 
lean_dec(v___x_2797_);
lean_dec_ref(v_trailing_2796_);
lean_dec(v_stx_2795_);
v___x_2834_ = lean_box(0);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2835_, lean_object* v_trailing_2836_){
_start:
{
lean_object* v___x_2837_; 
lean_inc(v_stx_2835_);
v___x_2837_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2835_, v_trailing_2836_);
if (lean_obj_tag(v___x_2837_) == 0)
{
return v_stx_2835_;
}
else
{
lean_object* v_val_2838_; 
lean_dec(v_stx_2835_);
v_val_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v___x_2837_, 1);
return v_val_2838_;
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

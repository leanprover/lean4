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
lean_dec_ref_known(v___y_1072_, 2);
lean_dec(v_info_1077_);
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
lean_inc_ref(v_fst_1115_);
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
lean_inc_ref(v_fst_1141_);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1278_, lean_object* v_pos_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
if (lean_obj_tag(v_a_1280_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = l_List_reverse___redArg(v_a_1281_);
return v___x_1282_;
}
else
{
lean_object* v_head_1283_; lean_object* v_tail_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1302_; 
v_head_1283_ = lean_ctor_get(v_a_1280_, 0);
v_tail_1284_ = lean_ctor_get(v_a_1280_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_a_1280_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1286_ = v_a_1280_;
v_isShared_1287_ = v_isSharedCheck_1302_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_tail_1284_);
lean_inc(v_head_1283_);
lean_dec(v_a_1280_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1302_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_stopPos_1288_; lean_object* v_startPos_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_info_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v_stopPos_1288_ = lean_ctor_get(v_head_1283_, 2);
lean_inc(v_stopPos_1288_);
lean_dec(v_head_1283_);
v_startPos_1289_ = lean_ctor_get(v_rawVal_1278_, 1);
v___x_1290_ = lean_nat_sub(v_stopPos_1288_, v_startPos_1289_);
lean_dec(v_stopPos_1288_);
v___x_1291_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1292_ = lean_nat_add(v___x_1290_, v_pos_1279_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_add(v___x_1293_, v___x_1292_);
v_info_1295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1295_, 0, v___x_1291_);
lean_ctor_set(v_info_1295_, 1, v___x_1292_);
lean_ctor_set(v_info_1295_, 2, v___x_1291_);
lean_ctor_set(v_info_1295_, 3, v___x_1294_);
v___x_1296_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_info_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v_a_1281_);
lean_ctor_set(v___x_1286_, 0, v___x_1297_);
v___x_1299_ = v___x_1286_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_a_1281_);
v___x_1299_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
v_a_1280_ = v_tail_1284_;
v_a_1281_ = v___x_1299_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1303_, lean_object* v_pos_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1303_, v_pos_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_pos_1304_);
lean_dec_ref(v_rawVal_1303_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1308_, lean_object* v_pos_1309_, lean_object* v_trailing_1310_, lean_object* v_leading_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
if (lean_obj_tag(v_a_1312_) == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_leading_1311_);
lean_dec_ref(v_trailing_1310_);
v___x_1314_ = l_List_reverse___redArg(v_a_1313_);
return v___x_1314_;
}
else
{
lean_object* v_head_1315_; lean_object* v_snd_1316_; lean_object* v_tail_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1347_; 
v_head_1315_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_head_1315_);
v_snd_1316_ = lean_ctor_get(v_head_1315_, 1);
lean_inc(v_snd_1316_);
v_tail_1317_ = lean_ctor_get(v_a_1312_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_a_1312_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_a_1312_, 0);
lean_dec(v_unused_1348_);
v___x_1319_ = v_a_1312_;
v_isShared_1320_ = v_isSharedCheck_1347_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_tail_1317_);
lean_dec(v_a_1312_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1347_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_fst_1321_; lean_object* v_startPos_1322_; lean_object* v_stopPos_1323_; lean_object* v_startPos_1324_; lean_object* v_stopPos_1325_; lean_object* v_off_1326_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1341_; lean_object* v___x_1344_; uint8_t v_decide_1345_; 
v_fst_1321_ = lean_ctor_get(v_head_1315_, 0);
lean_inc(v_fst_1321_);
lean_dec(v_head_1315_);
v_startPos_1322_ = lean_ctor_get(v_snd_1316_, 1);
v_stopPos_1323_ = lean_ctor_get(v_snd_1316_, 2);
v_startPos_1324_ = lean_ctor_get(v_rawVal_1308_, 1);
v_stopPos_1325_ = lean_ctor_get(v_rawVal_1308_, 2);
v_off_1326_ = lean_nat_sub(v_startPos_1322_, v_startPos_1324_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v_decide_1345_ = lean_nat_dec_eq(v_off_1326_, v___x_1344_);
if (v_decide_1345_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1341_ = v___x_1346_;
goto v___jp_1340_;
}
else
{
lean_inc_ref(v_leading_1311_);
v___y_1341_ = v_leading_1311_;
goto v___jp_1340_;
}
v___jp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_info_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1330_ = lean_nat_add(v_off_1326_, v_pos_1309_);
lean_dec(v_off_1326_);
v___x_1331_ = lean_nat_sub(v_stopPos_1323_, v_startPos_1322_);
v___x_1332_ = lean_nat_add(v___x_1331_, v___x_1330_);
lean_dec(v___x_1331_);
v_info_1333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1333_, 0, v___y_1328_);
lean_ctor_set(v_info_1333_, 1, v___x_1330_);
lean_ctor_set(v_info_1333_, 2, v___y_1329_);
lean_ctor_set(v_info_1333_, 3, v___x_1332_);
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1335_, 0, v_info_1333_);
lean_ctor_set(v___x_1335_, 1, v_snd_1316_);
lean_ctor_set(v___x_1335_, 2, v_fst_1321_);
lean_ctor_set(v___x_1335_, 3, v___x_1334_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_a_1313_);
lean_ctor_set(v___x_1319_, 0, v___x_1335_);
v___x_1337_ = v___x_1319_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_a_1313_);
v___x_1337_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v_a_1312_ = v_tail_1317_;
v_a_1313_ = v___x_1337_;
goto _start;
}
}
v___jp_1340_:
{
uint8_t v_decide_1342_; 
v_decide_1342_ = lean_nat_dec_eq(v_stopPos_1323_, v_stopPos_1325_);
if (v_decide_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1328_ = v___y_1341_;
v___y_1329_ = v___x_1343_;
goto v___jp_1327_;
}
else
{
lean_inc_ref(v_trailing_1310_);
v___y_1328_ = v___y_1341_;
v___y_1329_ = v_trailing_1310_;
goto v___jp_1327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1349_, lean_object* v_pos_1350_, lean_object* v_trailing_1351_, lean_object* v_leading_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1349_, v_pos_1350_, v_trailing_1351_, v_leading_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_pos_1350_);
lean_dec_ref(v_rawVal_1349_);
return v_res_1355_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__4(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1361_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1362_ = lean_unsigned_to_nat(9u);
v___x_1363_ = lean_unsigned_to_nat(342u);
v___x_1364_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1365_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1366_ = l_mkPanicMessageWithDecl(v___x_1365_, v___x_1364_, v___x_1363_, v___x_1362_, v___x_1361_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1367_, lean_object* v_nFields_x3f_1368_){
_start:
{
if (lean_obj_tag(v_stx_1367_) == 3)
{
lean_object* v_info_1369_; 
v_info_1369_ = lean_ctor_get(v_stx_1367_, 0);
lean_inc(v_info_1369_);
if (lean_obj_tag(v_info_1369_) == 0)
{
lean_object* v_rawVal_1370_; lean_object* v_val_1371_; lean_object* v_leading_1372_; lean_object* v_pos_1373_; lean_object* v_trailing_1374_; lean_object* v_rawComps_1375_; uint8_t v___x_1376_; 
v_rawVal_1370_ = lean_ctor_get(v_stx_1367_, 1);
lean_inc_ref_n(v_rawVal_1370_, 2);
v_val_1371_ = lean_ctor_get(v_stx_1367_, 2);
lean_inc(v_val_1371_);
lean_dec_ref_known(v_stx_1367_, 4);
v_leading_1372_ = lean_ctor_get(v_info_1369_, 0);
lean_inc_ref(v_leading_1372_);
v_pos_1373_ = lean_ctor_get(v_info_1369_, 1);
lean_inc(v_pos_1373_);
v_trailing_1374_ = lean_ctor_get(v_info_1369_, 2);
lean_inc_ref(v_trailing_1374_);
lean_dec_ref_known(v_info_1369_, 4);
v_rawComps_1375_ = l_Lean_Syntax_splitNameLit(v_rawVal_1370_);
v___x_1376_ = l_List_isEmpty___redArg(v_rawComps_1375_);
if (v___x_1376_ == 0)
{
lean_object* v_val_1377_; lean_object* v_nameComps_1378_; lean_object* v___y_1380_; 
v_val_1377_ = l_Lean_Name_eraseMacroScopes(v_val_1371_);
lean_dec(v_val_1371_);
v_nameComps_1378_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1377_, v_nFields_x3f_1368_);
if (lean_obj_tag(v_nFields_x3f_1368_) == 1)
{
lean_object* v_val_1394_; lean_object* v_str_1395_; lean_object* v_startPos_1396_; lean_object* v_stopPos_1397_; lean_object* v___x_1398_; lean_object* v_nPrefix_1399_; lean_object* v___y_1401_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_prefixSz_1407_; lean_object* v___x_1408_; lean_object* v_prefixSz_1409_; lean_object* v___y_1411_; uint8_t v___x_1416_; 
v_val_1394_ = lean_ctor_get(v_nFields_x3f_1368_, 0);
v_str_1395_ = lean_ctor_get(v_rawVal_1370_, 0);
v_startPos_1396_ = lean_ctor_get(v_rawVal_1370_, 1);
v_stopPos_1397_ = lean_ctor_get(v_rawVal_1370_, 2);
v___x_1398_ = l_List_lengthTR___redArg(v_rawComps_1375_);
v_nPrefix_1399_ = lean_nat_sub(v___x_1398_, v_val_1394_);
lean_dec(v___x_1398_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1399_);
lean_inc(v_rawComps_1375_);
v___x_1406_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1375_, v_rawComps_1375_, v_nPrefix_1399_, v___x_1405_);
v_prefixSz_1407_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1404_, v___x_1406_);
lean_dec(v___x_1406_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v_prefixSz_1409_ = lean_nat_sub(v_prefixSz_1407_, v___x_1408_);
lean_dec(v_prefixSz_1407_);
v___x_1416_ = lean_nat_dec_le(v_prefixSz_1409_, v___x_1404_);
if (v___x_1416_ == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_le(v_stopPos_1397_, v_startPos_1396_);
if (v___x_1417_ == 0)
{
lean_inc(v_startPos_1396_);
v___y_1411_ = v_startPos_1396_;
goto v___jp_1410_;
}
else
{
lean_inc(v_stopPos_1397_);
v___y_1411_ = v_stopPos_1397_;
goto v___jp_1410_;
}
}
else
{
lean_object* v___x_1418_; 
lean_dec(v_prefixSz_1409_);
v___x_1418_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1401_ = v___x_1418_;
goto v___jp_1400_;
}
v___jp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = l_List_drop___redArg(v_nPrefix_1399_, v_rawComps_1375_);
lean_dec(v_rawComps_1375_);
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___y_1380_ = v___x_1403_;
goto v___jp_1379_;
}
v___jp_1410_:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_nat_add(v_startPos_1396_, v_prefixSz_1409_);
lean_dec(v_prefixSz_1409_);
v___x_1413_ = lean_nat_dec_le(v_stopPos_1397_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_inc_ref(v_str_1395_);
v___x_1414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1414_, 0, v_str_1395_);
lean_ctor_set(v___x_1414_, 1, v___y_1411_);
lean_ctor_set(v___x_1414_, 2, v___x_1412_);
v___y_1401_ = v___x_1414_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1415_; 
lean_dec(v___x_1412_);
lean_inc(v_stopPos_1397_);
lean_inc_ref(v_str_1395_);
v___x_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1415_, 0, v_str_1395_);
lean_ctor_set(v___x_1415_, 1, v___y_1411_);
lean_ctor_set(v___x_1415_, 2, v_stopPos_1397_);
v___y_1401_ = v___x_1415_;
goto v___jp_1400_;
}
}
}
else
{
v___y_1380_ = v_rawComps_1375_;
goto v___jp_1379_;
}
v___jp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1381_ = l_List_lengthTR___redArg(v_nameComps_1378_);
v___x_1382_ = l_List_lengthTR___redArg(v___y_1380_);
v___x_1383_ = lean_nat_dec_eq(v___x_1381_, v___x_1382_);
lean_dec(v___x_1382_);
lean_dec(v___x_1381_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec(v___y_1380_);
lean_dec(v_nameComps_1378_);
lean_dec_ref(v_trailing_1374_);
lean_dec(v_pos_1373_);
lean_dec_ref(v_leading_1372_);
lean_dec_ref(v_rawVal_1370_);
v___x_1384_ = lean_box(0);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_comps_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_seps_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc(v___y_1380_);
v___x_1385_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1378_, v___y_1380_);
v___x_1386_ = lean_box(0);
v_comps_1387_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1370_, v_pos_1373_, v_trailing_1374_, v_leading_1372_, v___x_1385_, v___x_1386_);
v___x_1388_ = lean_array_mk(v___y_1380_);
v___x_1389_ = lean_array_pop(v___x_1388_);
v___x_1390_ = lean_array_to_list(v___x_1389_);
v_seps_1391_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1370_, v_pos_1373_, v___x_1390_, v___x_1386_);
lean_dec(v_pos_1373_);
lean_dec_ref(v_rawVal_1370_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_comps_1387_);
lean_ctor_set(v___x_1392_, 1, v_seps_1391_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
else
{
lean_object* v___x_1419_; 
lean_dec(v_rawComps_1375_);
lean_dec_ref(v_trailing_1374_);
lean_dec(v_pos_1373_);
lean_dec_ref(v_leading_1372_);
lean_dec(v_val_1371_);
lean_dec_ref(v_rawVal_1370_);
v___x_1419_ = lean_box(0);
return v___x_1419_;
}
}
else
{
lean_object* v___x_1420_; 
lean_dec_ref_known(v_stx_1367_, 4);
lean_dec(v_info_1369_);
v___x_1420_ = lean_box(0);
return v___x_1420_;
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v_stx_1367_);
v___x_1421_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__4, &l_Lean_Syntax_identComponents_x3f___closed__4_once, _init_l_Lean_Syntax_identComponents_x3f___closed__4);
v___x_1422_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1421_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1423_, lean_object* v_nFields_x3f_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Syntax_identComponents_x3f(v_stx_1423_, v_nFields_x3f_1424_);
lean_dec(v_nFields_x3f_1424_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1426_, lean_object* v_nFields_x3f_1427_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1427_) == 1)
{
lean_object* v_val_1428_; lean_object* v_nameComps_1429_; lean_object* v___x_1430_; lean_object* v_nPrefix_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_namePrefix_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_val_1428_ = lean_ctor_get(v_nFields_x3f_1427_, 0);
v_nameComps_1429_ = l_Lean_Name_components(v_n_1426_);
v___x_1430_ = l_List_lengthTR___redArg(v_nameComps_1429_);
v_nPrefix_1431_ = lean_nat_sub(v___x_1430_, v_val_1428_);
lean_dec(v___x_1430_);
v___x_1432_ = lean_box(0);
v___x_1433_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1431_);
lean_inc(v_nameComps_1429_);
v___x_1434_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1429_, v_nameComps_1429_, v_nPrefix_1431_, v___x_1433_);
v_namePrefix_1435_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1432_, v___x_1434_);
v___x_1436_ = l_List_drop___redArg(v_nPrefix_1431_, v_nameComps_1429_);
lean_dec(v_nameComps_1429_);
v___x_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_namePrefix_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Name_components(v_n_1426_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1439_, lean_object* v_nFields_x3f_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1439_, v_nFields_x3f_1440_);
lean_dec(v_nFields_x3f_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_panic_fn_borrowed(v___x_1443_, v_msg_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
if (lean_obj_tag(v_a_1446_) == 0)
{
lean_object* v___x_1448_; 
lean_dec(v_info_1445_);
v___x_1448_ = l_List_reverse___redArg(v_a_1447_);
return v___x_1448_;
}
else
{
lean_object* v_head_1449_; lean_object* v_tail_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1465_; 
v_head_1449_ = lean_ctor_get(v_a_1446_, 0);
v_tail_1450_ = lean_ctor_get(v_a_1446_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1446_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1452_ = v_a_1446_;
v_isShared_1453_ = v_isSharedCheck_1465_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_tail_1450_);
lean_inc(v_head_1449_);
lean_dec(v_a_1446_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1465_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1454_ = 1;
lean_inc(v_head_1449_);
v___x_1455_ = l_Lean_Name_toString(v_head_1449_, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_string_utf8_byte_size(v___x_1455_);
v___x_1458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1455_);
lean_ctor_set(v___x_1458_, 1, v___x_1456_);
lean_ctor_set(v___x_1458_, 2, v___x_1457_);
v___x_1459_ = lean_box(0);
lean_inc(v_info_1445_);
v___x_1460_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1460_, 0, v_info_1445_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
lean_ctor_set(v___x_1460_, 2, v_head_1449_);
lean_ctor_set(v___x_1460_, 3, v___x_1459_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v_a_1447_);
lean_ctor_set(v___x_1452_, 0, v___x_1460_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_a_1447_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
v_a_1446_ = v_tail_1450_;
v_a_1447_ = v___x_1462_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1468_ = lean_unsigned_to_nat(9u);
v___x_1469_ = lean_unsigned_to_nat(377u);
v___x_1470_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1471_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1473_, lean_object* v_nFields_x3f_1474_){
_start:
{
if (lean_obj_tag(v_stx_1473_) == 3)
{
lean_object* v_info_1475_; lean_object* v_rawVal_1476_; lean_object* v_val_1477_; lean_object* v_val_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_info_1475_ = lean_ctor_get(v_stx_1473_, 0);
lean_inc(v_info_1475_);
v_rawVal_1476_ = lean_ctor_get(v_stx_1473_, 1);
v_val_1477_ = lean_ctor_get(v_stx_1473_, 2);
v_val_1478_ = l_Lean_Name_eraseMacroScopes(v_val_1477_);
v___x_1479_ = l_Lean_Name_getNumParts(v_val_1478_);
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_dec_le(v___x_1479_, v___x_1480_);
lean_dec(v___x_1479_);
if (v___x_1481_ == 0)
{
if (lean_obj_tag(v_info_1475_) == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Syntax_identComponents_x3f(v_stx_1473_, v_nFields_x3f_1474_);
if (lean_obj_tag(v___x_1482_) == 1)
{
lean_object* v_val_1483_; lean_object* v_fst_1484_; 
lean_dec_ref_known(v_info_1475_, 4);
lean_dec(v_val_1478_);
v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v_fst_1484_ = lean_ctor_get(v_val_1483_, 0);
lean_inc(v_fst_1484_);
lean_dec(v_val_1483_);
return v_fst_1484_;
}
else
{
lean_object* v_nameComps_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v___x_1482_);
v_nameComps_1485_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1478_, v_nFields_x3f_1474_);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1475_, v_nameComps_1485_, v___x_1486_);
return v___x_1487_;
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref_known(v_stx_1473_, 4);
v___x_1488_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1478_, v_nFields_x3f_1474_);
v___x_1489_ = lean_box(0);
v___x_1490_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1475_, v___x_1488_, v___x_1489_);
return v___x_1490_;
}
}
else
{
lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1499_; 
lean_inc_ref(v_rawVal_1476_);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_stx_1473_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1500_ = lean_ctor_get(v_stx_1473_, 3);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_stx_1473_, 2);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_stx_1473_, 1);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_stx_1473_, 0);
lean_dec(v_unused_1503_);
v___x_1492_ = v_stx_1473_;
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v_stx_1473_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_box(0);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 3, v___x_1494_);
lean_ctor_set(v___x_1492_, 2, v_val_1478_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_info_1475_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_rawVal_1476_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_val_1478_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___x_1494_);
return v___x_1497_;
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_stx_1473_);
v___x_1504_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1505_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1504_);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1506_, lean_object* v_nFields_x3f_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Syntax_identComponents(v_stx_1506_, v_nFields_x3f_1507_);
lean_dec(v_nFields_x3f_1507_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1509_, uint8_t v_firstChoiceOnly_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1511_, 0, v_stx_1509_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*1, v_firstChoiceOnly_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1512_, lean_object* v_firstChoiceOnly_1513_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1514_; lean_object* v_res_1515_; 
v_firstChoiceOnly_boxed_1514_ = lean_unbox(v_firstChoiceOnly_1513_);
v_res_1515_ = l_Lean_Syntax_topDown(v_stx_1512_, v_firstChoiceOnly_boxed_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1516_, lean_object* v_____r_1517_, lean_object* v_b_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_b_1518_);
v___x_1520_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1521_, lean_object* v_toPure_1522_, lean_object* v_____s_1523_){
_start:
{
lean_object* v_fst_1524_; 
v_fst_1524_ = lean_ctor_get(v_____s_1523_, 0);
if (lean_obj_tag(v_fst_1524_) == 0)
{
lean_object* v_snd_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_toPure_1522_);
v_snd_1525_ = lean_ctor_get(v_____s_1523_, 1);
lean_inc(v_snd_1525_);
lean_dec_ref(v_____s_1523_);
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_apply_2(v___f_1521_, v___x_1526_, v_snd_1525_);
return v___x_1527_;
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1529_; 
lean_inc_ref(v_fst_1524_);
lean_dec_ref(v_____s_1523_);
lean_dec(v___f_1521_);
v_val_1528_ = lean_ctor_get(v_fst_1524_, 0);
lean_inc(v_val_1528_);
lean_dec_ref_known(v_fst_1524_, 1);
v___x_1529_ = lean_apply_2(v_toPure_1522_, lean_box(0), v_val_1528_);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1530_, lean_object* v_toPure_1531_, lean_object* v___x_1532_, lean_object* v_____do__lift_1533_){
_start:
{
if (lean_obj_tag(v_____do__lift_1533_) == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_____do__lift_1533_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_snd_1530_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
v___x_1537_ = lean_apply_2(v_toPure_1531_, lean_box(0), v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_snd_1530_);
v_a_1538_ = lean_ctor_get(v_____do__lift_1533_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_____do__lift_1533_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1540_ = v_____do__lift_1533_;
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v_____do__lift_1533_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1532_);
lean_ctor_set(v___x_1542_, 1, v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_apply_2(v_toPure_1531_, lean_box(0), v___x_1544_);
return v___x_1545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1548_, lean_object* v___x_1549_, lean_object* v_inst_1550_, lean_object* v_f_1551_, lean_object* v_firstChoiceOnly_1552_, lean_object* v_toBind_1553_, lean_object* v_a_1554_, lean_object* v_x_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1557_; lean_object* v_res_1558_; 
v_firstChoiceOnly_boxed_1557_ = lean_unbox(v_firstChoiceOnly_1552_);
v_res_1558_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1548_, v___x_1549_, v_inst_1550_, v_f_1551_, v_firstChoiceOnly_boxed_1557_, v_toBind_1553_, v_a_1554_, v_x_1555_, v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1562_, lean_object* v_stx_1563_, lean_object* v_inst_1564_, lean_object* v_f_1565_, uint8_t v_firstChoiceOnly_1566_, lean_object* v_toBind_1567_, lean_object* v___f_1568_, lean_object* v___x_1569_, lean_object* v___f_1570_, lean_object* v_____do__lift_1571_){
_start:
{
if (lean_obj_tag(v_____do__lift_1571_) == 0)
{
lean_object* v___x_1572_; 
lean_dec(v___f_1570_);
lean_dec(v___f_1568_);
lean_dec(v_toBind_1567_);
lean_dec(v_f_1565_);
lean_dec_ref(v_inst_1564_);
lean_dec(v_stx_1563_);
v___x_1572_ = lean_apply_2(v_toPure_1562_, lean_box(0), v_____do__lift_1571_);
return v___x_1572_;
}
else
{
if (lean_obj_tag(v_stx_1563_) == 1)
{
lean_object* v_a_1573_; lean_object* v_kind_1574_; lean_object* v_args_1575_; 
lean_dec(v___f_1570_);
v_a_1573_ = lean_ctor_get(v_____do__lift_1571_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v_____do__lift_1571_, 1);
v_kind_1574_ = lean_ctor_get(v_stx_1563_, 1);
lean_inc(v_kind_1574_);
v_args_1575_ = lean_ctor_get(v_stx_1563_, 2);
lean_inc_ref(v_args_1575_);
lean_dec_ref_known(v_stx_1563_, 3);
if (v_firstChoiceOnly_1566_ == 0)
{
lean_dec(v_kind_1574_);
goto v___jp_1576_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1586_ = lean_name_eq(v_kind_1574_, v___x_1585_);
lean_dec(v_kind_1574_);
if (v___x_1586_ == 0)
{
goto v___jp_1576_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v___f_1568_);
lean_dec(v_toBind_1567_);
lean_dec(v_toPure_1562_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_array_get(v___x_1569_, v_args_1575_, v___x_1587_);
lean_dec_ref(v_args_1575_);
v___x_1589_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1564_, v_f_1565_, v_firstChoiceOnly_1566_, v___x_1588_, v_a_1573_);
return v___x_1589_;
}
}
v___jp_1576_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___f_1579_; lean_object* v___x_1580_; size_t v_sz_1581_; size_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_box(v_firstChoiceOnly_1566_);
lean_inc(v_toBind_1567_);
lean_inc_ref(v_inst_1564_);
v___f_1579_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1579_, 0, v_toPure_1562_);
lean_closure_set(v___f_1579_, 1, v___x_1577_);
lean_closure_set(v___f_1579_, 2, v_inst_1564_);
lean_closure_set(v___f_1579_, 3, v_f_1565_);
lean_closure_set(v___f_1579_, 4, v___x_1578_);
lean_closure_set(v___f_1579_, 5, v_toBind_1567_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1577_);
lean_ctor_set(v___x_1580_, 1, v_a_1573_);
v_sz_1581_ = lean_array_size(v_args_1575_);
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1564_, v_args_1575_, v___f_1579_, v_sz_1581_, v___x_1582_, v___x_1580_);
v___x_1584_ = lean_apply_4(v_toBind_1567_, lean_box(0), lean_box(0), v___x_1583_, v___f_1568_);
return v___x_1584_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v___f_1568_);
lean_dec(v_toBind_1567_);
lean_dec(v_f_1565_);
lean_dec_ref(v_inst_1564_);
lean_dec(v_stx_1563_);
lean_dec(v_toPure_1562_);
v_a_1590_ = lean_ctor_get(v_____do__lift_1571_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v_____do__lift_1571_, 1);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_apply_2(v___f_1570_, v___x_1591_, v_a_1590_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1593_, lean_object* v_stx_1594_, lean_object* v_inst_1595_, lean_object* v_f_1596_, lean_object* v_firstChoiceOnly_1597_, lean_object* v_toBind_1598_, lean_object* v___f_1599_, lean_object* v___x_1600_, lean_object* v___f_1601_, lean_object* v_____do__lift_1602_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1603_; lean_object* v_res_1604_; 
v_firstChoiceOnly_boxed_1603_ = lean_unbox(v_firstChoiceOnly_1597_);
v_res_1604_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1593_, v_stx_1594_, v_inst_1595_, v_f_1596_, v_firstChoiceOnly_boxed_1603_, v_toBind_1598_, v___f_1599_, v___x_1600_, v___f_1601_, v_____do__lift_1602_);
lean_dec(v___x_1600_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1605_, lean_object* v_f_1606_, uint8_t v_firstChoiceOnly_1607_, lean_object* v_stx_1608_, lean_object* v_b_1609_){
_start:
{
lean_object* v_toApplicative_1610_; lean_object* v_toBind_1611_; lean_object* v_toPure_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; 
v_toApplicative_1610_ = lean_ctor_get(v_inst_1605_, 0);
v_toBind_1611_ = lean_ctor_get(v_inst_1605_, 1);
lean_inc_n(v_toBind_1611_, 2);
v_toPure_1612_ = lean_ctor_get(v_toApplicative_1610_, 1);
lean_inc_n(v_toPure_1612_, 3);
v___x_1613_ = lean_box(0);
lean_inc(v_f_1606_);
lean_inc(v_stx_1608_);
v___x_1614_ = lean_apply_2(v_f_1606_, v_stx_1608_, v_b_1609_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1615_, 0, v_toPure_1612_);
lean_inc_ref(v___f_1615_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1616_, 0, v___f_1615_);
lean_closure_set(v___f_1616_, 1, v_toPure_1612_);
v___x_1617_ = lean_box(v_firstChoiceOnly_1607_);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1618_, 0, v_toPure_1612_);
lean_closure_set(v___f_1618_, 1, v_stx_1608_);
lean_closure_set(v___f_1618_, 2, v_inst_1605_);
lean_closure_set(v___f_1618_, 3, v_f_1606_);
lean_closure_set(v___f_1618_, 4, v___x_1617_);
lean_closure_set(v___f_1618_, 5, v_toBind_1611_);
lean_closure_set(v___f_1618_, 6, v___f_1616_);
lean_closure_set(v___f_1618_, 7, v___x_1613_);
lean_closure_set(v___f_1618_, 8, v___f_1615_);
v___x_1619_ = lean_apply_4(v_toBind_1611_, lean_box(0), lean_box(0), v___x_1614_, v___f_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1620_, lean_object* v___x_1621_, lean_object* v_inst_1622_, lean_object* v_f_1623_, uint8_t v_firstChoiceOnly_1624_, lean_object* v_toBind_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_snd_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_snd_1629_ = lean_ctor_get(v___y_1628_, 1);
lean_inc_n(v_snd_1629_, 2);
lean_dec_ref(v___y_1628_);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1630_, 0, v_snd_1629_);
lean_closure_set(v___f_1630_, 1, v_toPure_1620_);
lean_closure_set(v___f_1630_, 2, v___x_1621_);
v___x_1631_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1622_, v_f_1623_, v_firstChoiceOnly_1624_, v_a_1626_, v_snd_1629_);
v___x_1632_ = lean_apply_4(v_toBind_1625_, lean_box(0), lean_box(0), v___x_1631_, v___f_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_firstChoiceOnly_1635_, lean_object* v_stx_1636_, lean_object* v_b_1637_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1638_; lean_object* v_res_1639_; 
v_firstChoiceOnly_boxed_1638_ = lean_unbox(v_firstChoiceOnly_1635_);
v_res_1639_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1633_, v_f_1634_, v_firstChoiceOnly_boxed_1638_, v_stx_1636_, v_b_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1640_, lean_object* v_inst_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_f_1643_, uint8_t v_firstChoiceOnly_1644_, lean_object* v_stx_1645_, lean_object* v_b_1646_, lean_object* v_inst_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1641_, v_f_1643_, v_firstChoiceOnly_1644_, v_stx_1645_, v_b_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1649_, lean_object* v_inst_1650_, lean_object* v_00_u03b2_1651_, lean_object* v_f_1652_, lean_object* v_firstChoiceOnly_1653_, lean_object* v_stx_1654_, lean_object* v_b_1655_, lean_object* v_inst_1656_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1657_; lean_object* v_res_1658_; 
v_firstChoiceOnly_boxed_1657_ = lean_unbox(v_firstChoiceOnly_1653_);
v_res_1658_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1649_, v_inst_1650_, v_00_u03b2_1651_, v_f_1652_, v_firstChoiceOnly_boxed_1657_, v_stx_1654_, v_b_1655_, v_inst_1656_);
lean_dec(v_inst_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1659_, lean_object* v_____do__lift_1660_){
_start:
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v_____do__lift_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v_____do__lift_1660_);
v___x_1662_ = lean_apply_2(v_toPure_1659_, lean_box(0), v_a_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1663_, lean_object* v_toBind_1664_, lean_object* v___f_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_x_1667_, lean_object* v_init_1668_, lean_object* v_f_1669_){
_start:
{
uint8_t v_firstChoiceOnly_1670_; lean_object* v_stx_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_firstChoiceOnly_1670_ = lean_ctor_get_uint8(v_x_1667_, sizeof(void*)*1);
v_stx_1671_ = lean_ctor_get(v_x_1667_, 0);
lean_inc(v_stx_1671_);
lean_dec_ref(v_x_1667_);
v___x_1672_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1663_, v_f_1669_, v_firstChoiceOnly_1670_, v_stx_1671_, v_init_1668_);
v___x_1673_ = lean_apply_4(v_toBind_1664_, lean_box(0), lean_box(0), v___x_1672_, v___f_1665_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1674_){
_start:
{
lean_object* v_toApplicative_1675_; lean_object* v_toBind_1676_; lean_object* v_toPure_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; 
v_toApplicative_1675_ = lean_ctor_get(v_inst_1674_, 0);
v_toBind_1676_ = lean_ctor_get(v_inst_1674_, 1);
lean_inc(v_toBind_1676_);
v_toPure_1677_ = lean_ctor_get(v_toApplicative_1675_, 1);
lean_inc(v_toPure_1677_);
v___f_1678_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1678_, 0, v_toPure_1677_);
v___f_1679_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1679_, 0, v_inst_1674_);
lean_closure_set(v___f_1679_, 1, v_toBind_1676_);
lean_closure_set(v___f_1679_, 2, v___f_1678_);
return v___f_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1680_, lean_object* v_inst_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1684_, lean_object* v_val_1685_){
_start:
{
if (lean_obj_tag(v_info_1684_) == 0)
{
lean_object* v_leading_1686_; lean_object* v_trailing_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_leading_1686_ = lean_ctor_get(v_info_1684_, 0);
lean_inc_ref(v_leading_1686_);
v_trailing_1687_ = lean_ctor_get(v_info_1684_, 2);
lean_inc_ref(v_trailing_1687_);
lean_dec_ref_known(v_info_1684_, 4);
v___x_1688_ = lean_substring_tostring(v_leading_1686_);
v___x_1689_ = lean_string_append(v___x_1688_, v_val_1685_);
v___x_1690_ = lean_substring_tostring(v_trailing_1687_);
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
lean_dec_ref(v___x_1690_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v_info_1684_);
v___x_1692_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1693_ = lean_string_append(v___x_1692_, v_val_1685_);
v___x_1694_ = lean_string_append(v___x_1693_, v___x_1692_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1695_, lean_object* v_val_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1695_, v_val_1696_);
lean_dec_ref(v_val_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1698_, lean_object* v_as_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_b_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_b_1702_);
return v___x_1704_;
}
else
{
lean_object* v_snd_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1732_; 
v_snd_1705_ = lean_ctor_get(v_b_1702_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_b_1702_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v_b_1702_, 0);
lean_dec(v_unused_1733_);
v___x_1707_ = v_b_1702_;
v_isShared_1708_ = v_isSharedCheck_1732_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1705_);
lean_dec(v_b_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1732_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_a_1709_; lean_object* v___x_1710_; 
v_a_1709_ = lean_array_uget_borrowed(v_as_1699_, v_i_1701_);
lean_inc(v_snd_1705_);
lean_inc(v_a_1709_);
v___x_1710_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1698_, v_a_1709_, v_snd_1705_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v___x_1711_; 
lean_del_object(v___x_1707_);
lean_dec(v_snd_1705_);
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
else
{
lean_object* v_val_1712_; 
v_val_1712_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_val_1712_);
if (lean_obj_tag(v_val_1712_) == 0)
{
lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1722_; 
v_isSharedCheck_1722_ = !lean_is_exclusive(v_val_1712_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v_val_1712_, 0);
lean_dec(v_unused_1723_);
v___x_1714_ = v_val_1712_;
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v_val_1712_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1710_);
v___x_1717_ = v___x_1707_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_snd_1705_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
lean_ctor_set(v___x_1714_, 0, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec_ref_known(v___x_1710_, 1);
lean_dec(v_snd_1705_);
v_a_1724_ = lean_ctor_get(v_val_1712_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v_val_1712_, 1);
v___x_1725_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_a_1724_);
lean_ctor_set(v___x_1707_, 0, v___x_1725_);
v___x_1727_ = v___x_1707_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_a_1724_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
size_t v___x_1728_; size_t v___x_1729_; 
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1701_, v___x_1728_);
v_i_1701_ = v___x_1729_;
v_b_1702_ = v___x_1727_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1734_, lean_object* v_a_1735_, lean_object* v_b_1736_){
_start:
{
lean_object* v_array_1737_; lean_object* v_start_1738_; lean_object* v_stop_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1758_; 
v_array_1737_ = lean_ctor_get(v_a_1735_, 0);
v_start_1738_ = lean_ctor_get(v_a_1735_, 1);
v_stop_1739_ = lean_ctor_get(v_a_1735_, 2);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_a_1735_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1741_ = v_a_1735_;
v_isShared_1742_ = v_isSharedCheck_1758_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_stop_1739_);
lean_inc(v_start_1738_);
lean_inc(v_array_1737_);
lean_dec(v_a_1735_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1758_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_lt(v_start_1738_, v_stop_1739_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_del_object(v___x_1741_);
lean_dec(v_stop_1739_);
lean_dec(v_start_1738_);
lean_dec_ref(v_array_1737_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1736_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_array_fget_borrowed(v_array_1737_, v_start_1738_);
lean_inc(v___x_1745_);
v___x_1746_ = l_Lean_Syntax_reprint(v___x_1745_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; 
lean_del_object(v___x_1741_);
lean_dec(v_stop_1739_);
lean_dec(v_start_1738_);
lean_dec_ref(v_array_1737_);
v___x_1747_ = lean_box(0);
return v___x_1747_;
}
else
{
lean_object* v_val_1748_; uint8_t v___x_1749_; 
v_val_1748_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1749_ = lean_string_dec_eq(v_val_1734_, v_val_1748_);
lean_dec(v_val_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_del_object(v___x_1741_);
lean_dec(v_stop_1739_);
lean_dec(v_start_1738_);
lean_dec_ref(v_array_1737_);
v___x_1750_ = lean_box(0);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_start_1738_, v___x_1752_);
lean_dec(v_start_1738_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 1, v___x_1753_);
v___x_1755_ = v___x_1741_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_array_1737_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_stop_1739_);
v___x_1755_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
v_a_1735_ = v___x_1755_;
v_b_1736_ = v___x_1751_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1759_, lean_object* v_stx_1760_, lean_object* v_b_1761_){
_start:
{
lean_object* v_b_1763_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___x_1777_; lean_object* v_a_1779_; 
v___x_1777_ = lean_box(0);
switch(lean_obj_tag(v_stx_1760_))
{
case 2:
{
lean_object* v_info_1788_; lean_object* v_val_1789_; lean_object* v___x_1790_; lean_object* v_s_1791_; 
v_info_1788_ = lean_ctor_get(v_stx_1760_, 0);
v_val_1789_ = lean_ctor_get(v_stx_1760_, 1);
lean_inc(v_info_1788_);
v___x_1790_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1788_, v_val_1789_);
v_s_1791_ = lean_string_append(v_b_1761_, v___x_1790_);
lean_dec_ref(v___x_1790_);
v_a_1779_ = v_s_1791_;
goto v___jp_1778_;
}
case 3:
{
lean_object* v_rawVal_1792_; lean_object* v_info_1793_; lean_object* v_str_1794_; lean_object* v_startPos_1795_; lean_object* v_stopPos_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_s_1799_; 
v_rawVal_1792_ = lean_ctor_get(v_stx_1760_, 1);
v_info_1793_ = lean_ctor_get(v_stx_1760_, 0);
v_str_1794_ = lean_ctor_get(v_rawVal_1792_, 0);
v_startPos_1795_ = lean_ctor_get(v_rawVal_1792_, 1);
v_stopPos_1796_ = lean_ctor_get(v_rawVal_1792_, 2);
v___x_1797_ = lean_string_utf8_extract(v_str_1794_, v_startPos_1795_, v_stopPos_1796_);
lean_inc(v_info_1793_);
v___x_1798_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1793_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v_s_1799_ = lean_string_append(v_b_1761_, v___x_1798_);
lean_dec_ref(v___x_1798_);
v_a_1779_ = v_s_1799_;
goto v___jp_1778_;
}
case 1:
{
lean_object* v_kind_1800_; lean_object* v_args_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_kind_1800_ = lean_ctor_get(v_stx_1760_, 1);
v_args_1801_ = lean_ctor_get(v_stx_1760_, 2);
v___x_1802_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1803_ = lean_name_eq(v_kind_1800_, v___x_1802_);
if (v___x_1803_ == 0)
{
v_a_1779_ = v_b_1761_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_array_get_borrowed(v___x_1777_, v_args_1801_, v___x_1804_);
lean_inc(v___x_1805_);
v___x_1806_ = l_Lean_Syntax_reprint(v___x_1805_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref_known(v_stx_1760_, 3);
lean_dec_ref(v_b_1761_);
v___x_1807_ = lean_box(0);
return v___x_1807_;
}
else
{
lean_object* v_val_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_val_1808_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v___x_1806_, 1);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_array_get_size(v_args_1801_);
lean_inc_ref(v_args_1801_);
v___x_1811_ = l_Array_toSubarray___redArg(v_args_1801_, v___x_1809_, v___x_1810_);
v___x_1812_ = lean_box(0);
v___x_1813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1808_, v___x_1811_, v___x_1812_);
lean_dec(v_val_1808_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; 
lean_dec_ref_known(v_stx_1760_, 3);
lean_dec_ref(v_b_1761_);
v___x_1814_ = lean_box(0);
return v___x_1814_;
}
else
{
lean_dec_ref_known(v___x_1813_, 1);
v_a_1779_ = v_b_1761_;
goto v___jp_1778_;
}
}
}
}
default: 
{
v_a_1779_ = v_b_1761_;
goto v___jp_1778_;
}
}
v___jp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_b_1763_);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
v___jp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; size_t v_sz_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v___y_1768_);
v_sz_1771_ = lean_array_size(v___y_1767_);
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1759_, v___y_1767_, v_sz_1771_, v___x_1772_, v___x_1770_);
lean_dec_ref(v___y_1767_);
if (lean_obj_tag(v___x_1773_) == 0)
{
return v___x_1769_;
}
else
{
lean_object* v_val_1774_; lean_object* v_fst_1775_; 
v_val_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_val_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v_fst_1775_ = lean_ctor_get(v_val_1774_, 0);
if (lean_obj_tag(v_fst_1775_) == 0)
{
lean_object* v_snd_1776_; 
v_snd_1776_ = lean_ctor_get(v_val_1774_, 1);
lean_inc(v_snd_1776_);
lean_dec(v_val_1774_);
v_b_1763_ = v_snd_1776_;
goto v___jp_1762_;
}
else
{
lean_inc_ref(v_fst_1775_);
lean_dec(v_val_1774_);
return v_fst_1775_;
}
}
}
v___jp_1778_:
{
if (lean_obj_tag(v_stx_1760_) == 1)
{
if (v_firstChoiceOnly_1759_ == 0)
{
lean_object* v_args_1780_; 
v_args_1780_ = lean_ctor_get(v_stx_1760_, 2);
lean_inc_ref(v_args_1780_);
lean_dec_ref_known(v_stx_1760_, 3);
v___y_1767_ = v_args_1780_;
v___y_1768_ = v_a_1779_;
goto v___jp_1766_;
}
else
{
lean_object* v_kind_1781_; lean_object* v_args_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_kind_1781_ = lean_ctor_get(v_stx_1760_, 1);
lean_inc(v_kind_1781_);
v_args_1782_ = lean_ctor_get(v_stx_1760_, 2);
lean_inc_ref(v_args_1782_);
lean_dec_ref_known(v_stx_1760_, 3);
v___x_1783_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1784_ = lean_name_eq(v_kind_1781_, v___x_1783_);
lean_dec(v_kind_1781_);
if (v___x_1784_ == 0)
{
v___y_1767_ = v_args_1782_;
v___y_1768_ = v_a_1779_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_array_get(v___x_1777_, v_args_1782_, v___x_1785_);
lean_dec_ref(v_args_1782_);
v_stx_1760_ = v___x_1786_;
v_b_1761_ = v_a_1779_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1760_);
v_b_1763_ = v_a_1779_;
goto v___jp_1762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1815_){
_start:
{
lean_object* v_s_1816_; uint8_t v___x_1817_; lean_object* v___x_1818_; 
v_s_1816_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1817_ = 1;
v___x_1818_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1817_, v_stx_1815_, v_s_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_box(0);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_val_1820_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1822_ = v___x_1818_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_val_1820_);
lean_dec(v___x_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_a_1824_; lean_object* v___x_1826_; 
v_a_1824_ = lean_ctor_get(v_val_1820_, 0);
lean_inc(v_a_1824_);
lean_dec(v_val_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_a_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1829_, lean_object* v_a_1830_, lean_object* v_b_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1829_, v_a_1830_, v_b_1831_);
lean_dec_ref(v_val_1829_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1833_, lean_object* v_as_1834_, lean_object* v_sz_1835_, lean_object* v_i_1836_, lean_object* v_b_1837_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1838_; size_t v_sz_boxed_1839_; size_t v_i_boxed_1840_; lean_object* v_res_1841_; 
v_firstChoiceOnly_boxed_1838_ = lean_unbox(v_firstChoiceOnly_1833_);
v_sz_boxed_1839_ = lean_unbox_usize(v_sz_1835_);
lean_dec(v_sz_1835_);
v_i_boxed_1840_ = lean_unbox_usize(v_i_1836_);
lean_dec(v_i_1836_);
v_res_1841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1838_, v_as_1834_, v_sz_boxed_1839_, v_i_boxed_1840_, v_b_1837_);
lean_dec_ref(v_as_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1842_, lean_object* v_stx_1843_, lean_object* v_b_1844_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1845_; lean_object* v_res_1846_; 
v_firstChoiceOnly_boxed_1845_ = lean_unbox(v_firstChoiceOnly_1842_);
v_res_1846_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1845_, v_stx_1843_, v_b_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1847_, lean_object* v_inst_1848_, lean_object* v_R_1849_, lean_object* v_a_1850_, lean_object* v_b_1851_, lean_object* v_c_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1847_, v_a_1850_, v_b_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1854_, lean_object* v_inst_1855_, lean_object* v_R_1856_, lean_object* v_a_1857_, lean_object* v_b_1858_, lean_object* v_c_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1854_, v_inst_1855_, v_R_1856_, v_a_1857_, v_b_1858_, v_c_1859_);
lean_dec_ref(v_val_1854_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1869_, lean_object* v_stx_1870_){
_start:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = l_Lean_Syntax_isMissing(v_stx_1870_);
if (v___x_1872_ == 0)
{
if (lean_obj_tag(v_stx_1870_) == 1)
{
lean_object* v_kind_1873_; lean_object* v_args_1874_; 
v_kind_1873_ = lean_ctor_get(v_stx_1870_, 1);
v_args_1874_ = lean_ctor_get(v_stx_1870_, 2);
if (v_firstChoiceOnly_1869_ == 0)
{
goto v___jp_1875_;
}
else
{
lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1885_ = lean_name_eq(v_kind_1873_, v___x_1884_);
if (v___x_1885_ == 0)
{
goto v___jp_1875_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = lean_array_get_borrowed(v___x_1886_, v_args_1874_, v___x_1887_);
v_stx_1870_ = v___x_1888_;
goto _start;
}
}
v___jp_1875_:
{
lean_object* v___x_1876_; size_t v_sz_1877_; size_t v___x_1878_; lean_object* v___x_1879_; lean_object* v_fst_1880_; 
v___x_1876_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1877_ = lean_array_size(v_args_1874_);
v___x_1878_ = ((size_t)0ULL);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1869_, v_args_1874_, v_sz_1877_, v___x_1878_, v___x_1876_);
v_fst_1880_ = lean_ctor_get(v___x_1879_, 0);
if (lean_obj_tag(v_fst_1880_) == 0)
{
lean_object* v_snd_1881_; lean_object* v___x_1882_; 
v_snd_1881_ = lean_ctor_get(v___x_1879_, 1);
lean_inc(v_snd_1881_);
lean_dec_ref(v___x_1879_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_snd_1881_);
return v___x_1882_;
}
else
{
lean_object* v_val_1883_; 
lean_inc_ref(v_fst_1880_);
lean_dec_ref(v___x_1879_);
v_val_1883_ = lean_ctor_get(v_fst_1880_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v_fst_1880_, 1);
return v_val_1883_;
}
}
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1890_;
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1891_ = lean_box(v___x_1872_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1871_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1895_, lean_object* v_as_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_b_1899_){
_start:
{
uint8_t v___x_1900_; 
v___x_1900_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1900_ == 0)
{
return v_b_1899_;
}
else
{
lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1919_; 
v_snd_1901_ = lean_ctor_get(v_b_1899_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_b_1899_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v_b_1899_, 0);
lean_dec(v_unused_1920_);
v___x_1903_ = v_b_1899_;
v_isShared_1904_ = v_isSharedCheck_1919_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_dec(v_b_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1919_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_array_uget_borrowed(v_as_1896_, v_i_1898_);
v___x_1906_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1895_, v_a_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1907_);
v___x_1909_ = v___x_1903_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_snd_1901_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_dec(v_snd_1901_);
v_a_1911_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1912_ = lean_box(0);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v_a_1911_);
lean_ctor_set(v___x_1903_, 0, v___x_1912_);
v___x_1914_ = v___x_1903_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1911_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
size_t v___x_1915_; size_t v___x_1916_; 
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1898_, v___x_1915_);
v_i_1898_ = v___x_1916_;
v_b_1899_ = v___x_1914_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1921_, lean_object* v_as_1922_, lean_object* v_sz_1923_, lean_object* v_i_1924_, lean_object* v_b_1925_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1926_; size_t v_sz_boxed_1927_; size_t v_i_boxed_1928_; lean_object* v_res_1929_; 
v_firstChoiceOnly_boxed_1926_ = lean_unbox(v_firstChoiceOnly_1921_);
v_sz_boxed_1927_ = lean_unbox_usize(v_sz_1923_);
lean_dec(v_sz_1923_);
v_i_boxed_1928_ = lean_unbox_usize(v_i_1924_);
lean_dec(v_i_1924_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1926_, v_as_1922_, v_sz_boxed_1927_, v_i_boxed_1928_, v_b_1925_);
lean_dec_ref(v_as_1922_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1930_, lean_object* v_stx_1931_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1932_; lean_object* v_res_1933_; 
v_firstChoiceOnly_boxed_1932_ = lean_unbox(v_firstChoiceOnly_1930_);
v_res_1933_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1932_, v_stx_1931_);
lean_dec(v_stx_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1934_){
_start:
{
uint8_t v___x_1935_; lean_object* v___y_1937_; lean_object* v___x_1941_; lean_object* v_a_1942_; 
v___x_1935_ = 0;
v___x_1941_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1935_, v_stx_1934_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___y_1937_ = v_a_1942_;
goto v___jp_1936_;
v___jp_1936_:
{
lean_object* v_fst_1938_; 
v_fst_1938_ = lean_ctor_get(v___y_1937_, 0);
lean_inc(v_fst_1938_);
lean_dec_ref(v___y_1937_);
if (lean_obj_tag(v_fst_1938_) == 0)
{
return v___x_1935_;
}
else
{
lean_object* v_val_1939_; uint8_t v___x_1940_; 
v_val_1939_ = lean_ctor_get(v_fst_1938_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v_fst_1938_, 1);
v___x_1940_ = lean_unbox(v_val_1939_);
lean_dec(v_val_1939_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Lean_Syntax_hasMissing(v_stx_1943_);
lean_dec(v_stx_1943_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1946_, lean_object* v_stx_1947_, lean_object* v_b_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1946_, v_stx_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1950_, lean_object* v_stx_1951_, lean_object* v_b_1952_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1953_; lean_object* v_res_1954_; 
v_firstChoiceOnly_boxed_1953_ = lean_unbox(v_firstChoiceOnly_1950_);
v_res_1954_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1953_, v_stx_1951_, v_b_1952_);
lean_dec_ref(v_b_1952_);
lean_dec(v_stx_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1955_, uint8_t v_canonicalOnly_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_Syntax_getPos_x3f(v_stx_1955_, v_canonicalOnly_1956_);
if (lean_obj_tag(v___x_1957_) == 1)
{
lean_object* v_val_1958_; lean_object* v___x_1959_; 
v_val_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_val_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1955_, v_canonicalOnly_1956_);
if (lean_obj_tag(v___x_1959_) == 1)
{
lean_object* v_val_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1968_; 
v_val_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_val_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_val_1958_);
lean_ctor_set(v___x_1964_, 1, v_val_1960_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
else
{
lean_object* v___x_1969_; 
lean_dec(v___x_1959_);
lean_dec(v_val_1958_);
v___x_1969_ = lean_box(0);
return v___x_1969_;
}
}
else
{
lean_object* v___x_1970_; 
lean_dec(v___x_1957_);
v___x_1970_ = lean_box(0);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1971_, lean_object* v_canonicalOnly_1972_){
_start:
{
uint8_t v_canonicalOnly_boxed_1973_; lean_object* v_res_1974_; 
v_canonicalOnly_boxed_1973_ = lean_unbox(v_canonicalOnly_1972_);
v_res_1974_ = l_Lean_Syntax_getRange_x3f(v_stx_1971_, v_canonicalOnly_boxed_1973_);
lean_dec(v_stx_1971_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1975_, uint8_t v_canonicalOnly_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Syntax_getPos_x3f(v_stx_1975_, v_canonicalOnly_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_box(0);
return v___x_1978_;
}
else
{
lean_object* v_val_1979_; lean_object* v___x_1980_; 
v_val_1979_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1980_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1975_, v_canonicalOnly_1976_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1981_; 
lean_dec(v_val_1979_);
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
else
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
v_val_1982_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v___x_1980_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v___x_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_val_1979_);
lean_ctor_set(v___x_1986_, 1, v_val_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1991_, lean_object* v_canonicalOnly_1992_){
_start:
{
uint8_t v_canonicalOnly_boxed_1993_; lean_object* v_res_1994_; 
v_canonicalOnly_boxed_1993_ = lean_unbox(v_canonicalOnly_1992_);
v_res_1994_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1991_, v_canonicalOnly_boxed_1993_);
lean_dec(v_stx_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1995_, uint8_t v_canonical_1996_){
_start:
{
lean_object* v_start_1997_; lean_object* v_stop_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2007_; 
v_start_1997_ = lean_ctor_get(v_range_1995_, 0);
v_stop_1998_ = lean_ctor_get(v_range_1995_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_range_1995_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2000_ = v_range_1995_;
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_stop_1998_);
lean_inc(v_start_1997_);
lean_dec(v_range_1995_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2002_, 0, v_start_1997_);
lean_ctor_set(v___x_2002_, 1, v_stop_1998_);
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*2, v_canonical_1996_);
v___x_2003_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 2);
lean_ctor_set(v___x_2000_, 1, v___x_2003_);
lean_ctor_set(v___x_2000_, 0, v___x_2002_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2008_, lean_object* v_canonical_2009_){
_start:
{
uint8_t v_canonical_boxed_2010_; lean_object* v_res_2011_; 
v_canonical_boxed_2010_ = lean_unbox(v_canonical_2009_);
v_res_2011_ = l_Lean_Syntax_ofRange(v_range_2008_, v_canonical_boxed_2010_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2016_, 0, v_stx_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
lean_ctor_set(v___x_2016_, 2, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2017_, lean_object* v_stx_2018_){
_start:
{
lean_object* v_parents_2019_; lean_object* v_idxs_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_parents_2019_ = lean_ctor_get(v_t_2017_, 1);
v_idxs_2020_ = lean_ctor_get(v_t_2017_, 2);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_t_2017_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_t_2017_, 0);
lean_dec(v_unused_2028_);
v___x_2022_ = v_t_2017_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_idxs_2020_);
lean_inc(v_parents_2019_);
lean_dec(v_t_2017_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v_stx_2018_);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_stx_2018_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_parents_2019_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_idxs_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2029_, lean_object* v_idx_2030_){
_start:
{
lean_object* v_cur_2031_; lean_object* v_parents_2032_; lean_object* v_idxs_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2053_; 
v_cur_2031_ = lean_ctor_get(v_t_2029_, 0);
v_parents_2032_ = lean_ctor_get(v_t_2029_, 1);
v_idxs_2033_ = lean_ctor_get(v_t_2029_, 2);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_t_2029_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2035_ = v_t_2029_;
v_isShared_2036_ = v_isSharedCheck_2053_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_idxs_2033_);
lean_inc(v_parents_2032_);
lean_inc(v_cur_2031_);
lean_dec(v_t_2029_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2053_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = l_Lean_Syntax_getNumArgs(v_cur_2031_);
v___x_2038_ = lean_nat_dec_lt(v_idx_2030_, v___x_2037_);
lean_dec(v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_array_push(v_parents_2032_, v_cur_2031_);
v___x_2041_ = lean_array_push(v_idxs_2033_, v_idx_2030_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 2, v___x_2041_);
lean_ctor_set(v___x_2035_, 1, v___x_2040_);
lean_ctor_set(v___x_2035_, 0, v___x_2039_);
v___x_2043_ = v___x_2035_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2045_ = l_Lean_Syntax_getArg(v_cur_2031_, v_idx_2030_);
v___x_2046_ = lean_box(0);
v___x_2047_ = l_Lean_Syntax_setArg(v_cur_2031_, v_idx_2030_, v___x_2046_);
v___x_2048_ = lean_array_push(v_parents_2032_, v___x_2047_);
v___x_2049_ = lean_array_push(v_idxs_2033_, v_idx_2030_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 2, v___x_2049_);
lean_ctor_set(v___x_2035_, 1, v___x_2048_);
lean_ctor_set(v___x_2035_, 0, v___x_2045_);
v___x_2051_ = v___x_2035_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2054_){
_start:
{
lean_object* v_cur_2055_; lean_object* v_parents_2056_; lean_object* v_idxs_2057_; lean_object* v___y_2059_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_cur_2055_ = lean_ctor_get(v_t_2054_, 0);
v_parents_2056_ = lean_ctor_get(v_t_2054_, 1);
v_idxs_2057_ = lean_ctor_get(v_t_2054_, 2);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_array_get_size(v_parents_2056_);
v___x_2065_ = lean_nat_dec_lt(v___x_2063_, v___x_2064_);
if (v___x_2065_ == 0)
{
return v_t_2054_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
lean_inc_ref(v_idxs_2057_);
lean_inc_ref(v_parents_2056_);
lean_inc(v_cur_2055_);
lean_dec_ref(v_t_2054_);
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_array_get_size(v_idxs_2057_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_sub(v___x_2067_, v___x_2068_);
v___x_2070_ = lean_array_get_borrowed(v___x_2063_, v_idxs_2057_, v___x_2069_);
lean_dec(v___x_2069_);
v___x_2071_ = lean_nat_sub(v___x_2064_, v___x_2068_);
v___x_2072_ = lean_array_get_borrowed(v___x_2066_, v_parents_2056_, v___x_2071_);
lean_dec(v___x_2071_);
v___x_2073_ = l_Lean_Syntax_getNumArgs(v___x_2072_);
v___x_2074_ = lean_nat_dec_lt(v___x_2070_, v___x_2073_);
lean_dec(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_cur_2055_);
lean_inc(v___x_2072_);
v___y_2059_ = v___x_2072_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2075_; 
lean_inc(v___x_2072_);
v___x_2075_ = l_Lean_Syntax_setArg(v___x_2072_, v___x_2070_, v_cur_2055_);
v___y_2059_ = v___x_2075_;
goto v___jp_2058_;
}
}
v___jp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_array_pop(v_parents_2056_);
v___x_2061_ = lean_array_pop(v_idxs_2057_);
v___x_2062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2062_, 0, v___y_2059_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
lean_ctor_set(v___x_2062_, 2, v___x_2061_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2076_){
_start:
{
lean_object* v_parents_2077_; lean_object* v_idxs_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_parents_2077_ = lean_ctor_get(v_t_2076_, 1);
v_idxs_2078_ = lean_ctor_get(v_t_2076_, 2);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_array_get_size(v_parents_2077_);
v___x_2081_ = lean_nat_dec_lt(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
return v_t_2076_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_inc_ref(v_idxs_2078_);
v___x_2082_ = l_Lean_Syntax_Traverser_up(v_t_2076_);
v___x_2083_ = lean_array_get_size(v_idxs_2078_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_sub(v___x_2083_, v___x_2084_);
v___x_2086_ = lean_array_get(v___x_2079_, v_idxs_2078_, v___x_2085_);
lean_dec(v___x_2085_);
lean_dec_ref(v_idxs_2078_);
v___x_2087_ = lean_nat_sub(v___x_2086_, v___x_2084_);
lean_dec(v___x_2086_);
v___x_2088_ = l_Lean_Syntax_Traverser_down(v___x_2082_, v___x_2087_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2089_){
_start:
{
lean_object* v_parents_2090_; lean_object* v_idxs_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_parents_2090_ = lean_ctor_get(v_t_2089_, 1);
v_idxs_2091_ = lean_ctor_get(v_t_2089_, 2);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = lean_array_get_size(v_parents_2090_);
v___x_2094_ = lean_nat_dec_lt(v___x_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
return v_t_2089_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_inc_ref(v_idxs_2091_);
v___x_2095_ = l_Lean_Syntax_Traverser_up(v_t_2089_);
v___x_2096_ = lean_array_get_size(v_idxs_2091_);
v___x_2097_ = lean_unsigned_to_nat(1u);
v___x_2098_ = lean_nat_sub(v___x_2096_, v___x_2097_);
v___x_2099_ = lean_array_get(v___x_2092_, v_idxs_2091_, v___x_2098_);
lean_dec(v___x_2098_);
lean_dec_ref(v_idxs_2091_);
v___x_2100_ = lean_nat_add(v___x_2099_, v___x_2097_);
lean_dec(v___x_2099_);
v___x_2101_ = l_Lean_Syntax_Traverser_down(v___x_2095_, v___x_2100_);
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2102_){
_start:
{
lean_object* v_cur_2103_; 
v_cur_2103_ = lean_ctor_get(v_self_2102_, 0);
lean_inc(v_cur_2103_);
return v_cur_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2104_);
lean_dec_ref(v_self_2104_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2107_, lean_object* v_t_2108_){
_start:
{
lean_object* v_toApplicative_2109_; lean_object* v_toFunctor_2110_; lean_object* v_map_2111_; lean_object* v_get_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; 
v_toApplicative_2109_ = lean_ctor_get(v_inst_2107_, 0);
lean_inc_ref(v_toApplicative_2109_);
lean_dec_ref(v_inst_2107_);
v_toFunctor_2110_ = lean_ctor_get(v_toApplicative_2109_, 0);
lean_inc_ref(v_toFunctor_2110_);
lean_dec_ref(v_toApplicative_2109_);
v_map_2111_ = lean_ctor_get(v_toFunctor_2110_, 0);
lean_inc(v_map_2111_);
lean_dec_ref(v_toFunctor_2110_);
v_get_2112_ = lean_ctor_get(v_t_2108_, 0);
lean_inc(v_get_2112_);
lean_dec_ref(v_t_2108_);
v___f_2113_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2114_ = lean_apply_4(v_map_2111_, lean_box(0), lean_box(0), v___f_2113_, v_get_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2115_, lean_object* v_inst_2116_, lean_object* v_t_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2116_, v_t_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2119_, lean_object* v_s_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lean_Syntax_Traverser_setCur(v_s_2120_, v_stx_2119_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2124_, lean_object* v_stx_2125_){
_start:
{
lean_object* v_modifyGet_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; 
v_modifyGet_2126_ = lean_ctor_get(v_t_2124_, 2);
lean_inc(v_modifyGet_2126_);
lean_dec_ref(v_t_2124_);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2127_, 0, v_stx_2125_);
v___x_2128_ = lean_apply_2(v_modifyGet_2126_, lean_box(0), v___f_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2129_, lean_object* v_t_2130_, lean_object* v_stx_2131_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2130_, v_stx_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2133_, lean_object* v_s_2134_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = l_Lean_Syntax_Traverser_down(v_s_2134_, v_idx_2133_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2138_, lean_object* v_idx_2139_){
_start:
{
lean_object* v_modifyGet_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; 
v_modifyGet_2140_ = lean_ctor_get(v_t_2138_, 2);
lean_inc(v_modifyGet_2140_);
lean_dec_ref(v_t_2138_);
v___f_2141_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2141_, 0, v_idx_2139_);
v___x_2142_ = lean_apply_2(v_modifyGet_2140_, lean_box(0), v___f_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2143_, lean_object* v_t_2144_, lean_object* v_idx_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2144_, v_idx_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = l_Lean_Syntax_Traverser_up(v_s_2147_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2152_){
_start:
{
lean_object* v_modifyGet_2153_; lean_object* v___f_2154_; lean_object* v___x_2155_; 
v_modifyGet_2153_ = lean_ctor_get(v_t_2152_, 2);
lean_inc(v_modifyGet_2153_);
lean_dec_ref(v_t_2152_);
v___f_2154_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2155_ = lean_apply_2(v_modifyGet_2153_, lean_box(0), v___f_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2156_, lean_object* v_t_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_box(0);
v___x_2161_ = l_Lean_Syntax_Traverser_left(v_s_2159_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2164_){
_start:
{
lean_object* v_modifyGet_2165_; lean_object* v___f_2166_; lean_object* v___x_2167_; 
v_modifyGet_2165_ = lean_ctor_get(v_t_2164_, 2);
lean_inc(v_modifyGet_2165_);
lean_dec_ref(v_t_2164_);
v___f_2166_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2167_ = lean_apply_2(v_modifyGet_2165_, lean_box(0), v___f_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2168_, lean_object* v_t_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(0);
v___x_2173_ = l_Lean_Syntax_Traverser_right(v_s_2171_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2176_){
_start:
{
lean_object* v_modifyGet_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; 
v_modifyGet_2177_ = lean_ctor_get(v_t_2176_, 2);
lean_inc(v_modifyGet_2177_);
lean_dec_ref(v_t_2176_);
v___f_2178_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2179_ = lean_apply_2(v_modifyGet_2177_, lean_box(0), v___f_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2180_, lean_object* v_t_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2183_, lean_object* v_st_2184_){
_start:
{
lean_object* v_idxs_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_idxs_2185_ = lean_ctor_get(v_st_2184_, 2);
v___x_2186_ = lean_array_get_size(v_idxs_2185_);
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = lean_nat_sub(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_nat_dec_lt(v___x_2188_, v___x_2186_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v___x_2188_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_apply_2(v_toPure_2183_, lean_box(0), v___x_2190_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_array_fget_borrowed(v_idxs_2185_, v___x_2188_);
lean_dec(v___x_2188_);
lean_inc(v___x_2192_);
v___x_2193_ = lean_apply_2(v_toPure_2183_, lean_box(0), v___x_2192_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2194_, lean_object* v_st_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2194_, v_st_2195_);
lean_dec_ref(v_st_2195_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2197_, lean_object* v_t_2198_){
_start:
{
lean_object* v_toApplicative_2199_; lean_object* v_toBind_2200_; lean_object* v_get_2201_; lean_object* v_toPure_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
v_toApplicative_2199_ = lean_ctor_get(v_inst_2197_, 0);
lean_inc_ref(v_toApplicative_2199_);
v_toBind_2200_ = lean_ctor_get(v_inst_2197_, 1);
lean_inc(v_toBind_2200_);
lean_dec_ref(v_inst_2197_);
v_get_2201_ = lean_ctor_get(v_t_2198_, 0);
lean_inc(v_get_2201_);
lean_dec_ref(v_t_2198_);
v_toPure_2202_ = lean_ctor_get(v_toApplicative_2199_, 1);
lean_inc(v_toPure_2202_);
lean_dec_ref(v_toApplicative_2199_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2203_, 0, v_toPure_2202_);
v___x_2204_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v_get_2201_, v___f_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2205_, lean_object* v_inst_2206_, lean_object* v_t_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2206_, v_t_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2209_, lean_object* v_i_2210_){
_start:
{
lean_object* v_args_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_args_2211_ = lean_ctor_get(v_n_2209_, 2);
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_array_get_borrowed(v___x_2212_, v_args_2211_, v_i_2210_);
v___x_2214_ = l_Lean_Syntax_getId(v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2215_, lean_object* v_i_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_SyntaxNode_getIdAt(v_n_2215_, v_i_2216_);
lean_dec(v_i_2216_);
lean_dec(v_n_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2218_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2220_ = lean_box(2);
v___x_2221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2219_);
lean_ctor_set(v___x_2221_, 2, v_args_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2227_){
_start:
{
if (lean_obj_tag(v_x_2227_) == 1)
{
lean_object* v_kind_2228_; 
v_kind_2228_ = lean_ctor_get(v_x_2227_, 1);
if (lean_obj_tag(v_kind_2228_) == 1)
{
lean_object* v_pre_2229_; lean_object* v_str_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_pre_2229_ = lean_ctor_get(v_kind_2228_, 0);
v_str_2230_ = lean_ctor_get(v_kind_2228_, 1);
v___x_2231_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2232_ = lean_string_dec_eq(v_str_2230_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2234_ = lean_string_dec_eq(v_str_2230_, v___x_2233_);
if (v___x_2234_ == 0)
{
return v___x_2234_;
}
else
{
if (lean_obj_tag(v_pre_2229_) == 1)
{
lean_object* v_pre_2235_; 
v_pre_2235_ = lean_ctor_get(v_pre_2229_, 0);
if (lean_obj_tag(v_pre_2235_) == 1)
{
lean_object* v_pre_2236_; 
v_pre_2236_ = lean_ctor_get(v_pre_2235_, 0);
if (lean_obj_tag(v_pre_2236_) == 1)
{
lean_object* v_pre_2237_; 
v_pre_2237_ = lean_ctor_get(v_pre_2236_, 0);
if (lean_obj_tag(v_pre_2237_) == 0)
{
lean_object* v_str_2238_; lean_object* v_str_2239_; lean_object* v_str_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v_str_2238_ = lean_ctor_get(v_pre_2229_, 1);
v_str_2239_ = lean_ctor_get(v_pre_2235_, 1);
v_str_2240_ = lean_ctor_get(v_pre_2236_, 1);
v___x_2241_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2242_ = lean_string_dec_eq(v_str_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
return v___x_2232_;
}
else
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2244_ = lean_string_dec_eq(v_str_2239_, v___x_2243_);
if (v___x_2244_ == 0)
{
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2246_ = lean_string_dec_eq(v_str_2238_, v___x_2245_);
return v___x_2246_;
}
}
}
else
{
return v___x_2232_;
}
}
else
{
return v___x_2232_;
}
}
else
{
return v___x_2232_;
}
}
else
{
return v___x_2232_;
}
}
}
else
{
return v___x_2232_;
}
}
else
{
uint8_t v___x_2247_; 
v___x_2247_ = 0;
return v___x_2247_;
}
}
else
{
uint8_t v___x_2248_; 
v___x_2248_ = 0;
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2249_){
_start:
{
uint8_t v_res_2250_; lean_object* v_r_2251_; 
v_res_2250_ = l_Lean_Syntax_isQuot(v_x_2249_);
lean_dec(v_x_2249_);
v_r_2251_ = lean_box(v_res_2250_);
return v_r_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___y_2261_; uint8_t v___x_2267_; 
v___x_2258_ = l_Lean_Syntax_getNumArgs(v_stx_2257_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_dec_eq(v___x_2258_, v___x_2259_);
lean_dec(v___x_2258_);
if (v___x_2267_ == 0)
{
v___y_2261_ = v_stx_2257_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = l_Lean_Syntax_getArg(v_stx_2257_, v___x_2268_);
lean_dec(v_stx_2257_);
v___y_2261_ = v___x_2269_;
goto v___jp_2260_;
}
v___jp_2260_:
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2261_);
v___x_2263_ = l_Lean_Syntax_isOfKind(v___y_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Syntax_getArg(v___y_2261_, v___x_2259_);
lean_dec(v___y_2261_);
return v___x_2264_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_unsigned_to_nat(3u);
v___x_2266_ = l_Lean_Syntax_getArg(v___y_2261_, v___x_2265_);
lean_dec(v___y_2261_);
return v___x_2266_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 1)
{
lean_object* v_kind_2272_; 
v_kind_2272_ = lean_ctor_get(v_x_2271_, 1);
if (lean_obj_tag(v_kind_2272_) == 1)
{
lean_object* v_str_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_str_2273_ = lean_ctor_get(v_kind_2272_, 1);
v___x_2274_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2275_ = lean_string_dec_eq(v_str_2273_, v___x_2274_);
return v___x_2275_;
}
else
{
uint8_t v___x_2276_; 
v___x_2276_ = 0;
return v___x_2276_;
}
}
else
{
uint8_t v___x_2277_; 
v___x_2277_ = 0;
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2278_){
_start:
{
uint8_t v_res_2279_; lean_object* v_r_2280_; 
v_res_2279_ = l_Lean_Syntax_isAntiquot(v_x_2278_);
lean_dec(v_x_2278_);
v_r_2280_ = lean_box(v_res_2279_);
return v_r_2280_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2281_, uint8_t v___x_2282_, lean_object* v_as_2283_, size_t v_i_2284_, size_t v_stop_2285_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_usize_dec_eq(v_i_2284_, v_stop_2285_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; uint8_t v___y_2289_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2287_ = 1;
v___x_2293_ = lean_array_uget_borrowed(v_as_2283_, v_i_2284_);
v___x_2294_ = l_Lean_Syntax_isAntiquot(v___x_2293_);
if (v___x_2294_ == 0)
{
v___y_2289_ = v___y_2281_;
goto v___jp_2288_;
}
else
{
v___y_2289_ = v___x_2282_;
goto v___jp_2288_;
}
v___jp_2288_:
{
if (v___y_2289_ == 0)
{
size_t v___x_2290_; size_t v___x_2291_; 
v___x_2290_ = ((size_t)1ULL);
v___x_2291_ = lean_usize_add(v_i_2284_, v___x_2290_);
v_i_2284_ = v___x_2291_;
goto _start;
}
else
{
return v___x_2287_;
}
}
}
else
{
uint8_t v___x_2295_; 
v___x_2295_ = 0;
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2296_, lean_object* v___x_2297_, lean_object* v_as_2298_, lean_object* v_i_2299_, lean_object* v_stop_2300_){
_start:
{
uint8_t v___y_330__boxed_2301_; uint8_t v___x_331__boxed_2302_; size_t v_i_boxed_2303_; size_t v_stop_boxed_2304_; uint8_t v_res_2305_; lean_object* v_r_2306_; 
v___y_330__boxed_2301_ = lean_unbox(v___y_2296_);
v___x_331__boxed_2302_ = lean_unbox(v___x_2297_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2299_);
lean_dec(v_i_2299_);
v_stop_boxed_2304_ = lean_unbox_usize(v_stop_2300_);
lean_dec(v_stop_2300_);
v_res_2305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_330__boxed_2301_, v___x_331__boxed_2302_, v_as_2298_, v_i_boxed_2303_, v_stop_boxed_2304_);
lean_dec_ref(v_as_2298_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2307_){
_start:
{
uint8_t v___x_2308_; uint8_t v___y_2310_; 
v___x_2308_ = l_Lean_Syntax_isAntiquot(v_stx_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2307_);
v___x_2319_ = l_Lean_Syntax_isOfKind(v_stx_2307_, v___x_2318_);
if (v___x_2319_ == 0)
{
v___y_2310_ = v___x_2319_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = l_Lean_Syntax_getNumArgs(v_stx_2307_);
v___x_2322_ = lean_nat_dec_lt(v___x_2320_, v___x_2321_);
lean_dec(v___x_2321_);
v___y_2310_ = v___x_2322_;
goto v___jp_2309_;
}
}
else
{
lean_dec(v_stx_2307_);
return v___x_2308_;
}
v___jp_2309_:
{
if (v___y_2310_ == 0)
{
lean_dec(v_stx_2307_);
return v___y_2310_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2311_ = l_Lean_Syntax_getArgs(v_stx_2307_);
lean_dec(v_stx_2307_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_array_get_size(v___x_2311_);
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec_ref(v___x_2311_);
return v___y_2310_;
}
else
{
if (v___x_2314_ == 0)
{
lean_dec_ref(v___x_2311_);
return v___y_2310_;
}
else
{
size_t v___x_2315_; size_t v___x_2316_; uint8_t v___x_2317_; 
v___x_2315_ = ((size_t)0ULL);
v___x_2316_ = lean_usize_of_nat(v___x_2313_);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2310_, v___x_2308_, v___x_2311_, v___x_2315_, v___x_2316_);
lean_dec_ref(v___x_2311_);
if (v___x_2317_ == 0)
{
return v___x_2314_;
}
else
{
return v___x_2308_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2323_){
_start:
{
uint8_t v_res_2324_; lean_object* v_r_2325_; 
v_res_2324_ = l_Lean_Syntax_isAntiquots(v_stx_2323_);
v_r_2325_ = lean_box(v_res_2324_);
return v_r_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2326_){
_start:
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2326_);
v___x_2328_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2327_);
if (v___x_2328_ == 0)
{
return v_stx_2326_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2329_);
lean_dec(v_stx_2326_);
return v___x_2330_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2333_ = l_Lean_mkAtom(v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2336_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2337_ = lean_unsigned_to_nat(4u);
v___x_2338_ = lean_mk_empty_array_with_capacity(v___x_2337_);
v___x_2339_ = lean_array_push(v___x_2338_, v___x_2336_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2348_ = l_Lean_mkAtom(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2350_ = lean_unsigned_to_nat(2u);
v___x_2351_ = lean_mk_empty_array_with_capacity(v___x_2350_);
v___x_2352_ = lean_array_push(v___x_2351_, v___x_2349_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2364_ = l_Lean_mkAtom(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2367_ = l_Lean_mkAtom(v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2368_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2369_ = lean_unsigned_to_nat(3u);
v___x_2370_ = lean_mk_empty_array_with_capacity(v___x_2369_);
v___x_2371_ = lean_array_push(v___x_2370_, v___x_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2372_, lean_object* v_term_2373_, lean_object* v_nesting_2374_, lean_object* v_name_2375_, uint8_t v_isPseudoKind_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v_nesting_2381_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2400_; uint8_t v___x_2408_; 
v___x_2377_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2378_ = lean_mk_array(v_nesting_2374_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2380_ = lean_box(2);
v_nesting_2381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2381_, 0, v___x_2380_);
lean_ctor_set(v_nesting_2381_, 1, v___x_2379_);
lean_ctor_set(v_nesting_2381_, 2, v___x_2378_);
v___x_2408_ = l_Lean_Syntax_isIdent(v_term_2373_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2373_);
v___x_2410_ = l_Lean_Syntax_isOfKind(v_term_2373_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2411_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2412_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2413_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2414_ = lean_array_push(v___x_2413_, v_term_2373_);
v___x_2415_ = lean_array_push(v___x_2414_, v___x_2412_);
v___x_2416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2380_);
lean_ctor_set(v___x_2416_, 1, v___x_2411_);
lean_ctor_set(v___x_2416_, 2, v___x_2415_);
v___y_2400_ = v___x_2416_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = l_Lean_Syntax_getArg(v_term_2373_, v___x_2417_);
lean_dec(v_term_2373_);
v___y_2400_ = v___x_2418_;
goto v___jp_2399_;
}
}
else
{
v___y_2400_ = v_term_2373_;
goto v___jp_2399_;
}
v___jp_2382_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_inc(v___y_2385_);
v___x_2386_ = l_Lean_Name_append(v_kind_2372_, v___y_2385_);
v___x_2387_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2388_ = l_Lean_Name_append(v___x_2386_, v___x_2387_);
v___x_2389_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2390_ = lean_array_push(v___x_2389_, v_nesting_2381_);
v___x_2391_ = lean_array_push(v___x_2390_, v___y_2383_);
v___x_2392_ = lean_array_push(v___x_2391_, v___y_2384_);
v___x_2393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2380_);
lean_ctor_set(v___x_2393_, 1, v___x_2388_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
return v___x_2393_;
}
v___jp_2394_:
{
if (v_isPseudoKind_2376_ == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_box(0);
v___y_2383_ = v___y_2395_;
v___y_2384_ = v___y_2396_;
v___y_2385_ = v___x_2397_;
goto v___jp_2382_;
}
else
{
lean_object* v___x_2398_; 
v___x_2398_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2383_ = v___y_2395_;
v___y_2384_ = v___y_2396_;
v___y_2385_ = v___x_2398_;
goto v___jp_2382_;
}
}
v___jp_2399_:
{
if (lean_obj_tag(v_name_2375_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2395_ = v___y_2400_;
v___y_2396_ = v___x_2401_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_val_2402_ = lean_ctor_get(v_name_2375_, 0);
lean_inc(v_val_2402_);
lean_dec_ref_known(v_name_2375_, 1);
v___x_2403_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2404_ = l_Lean_mkAtom(v_val_2402_);
v___x_2405_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2406_ = lean_array_push(v___x_2405_, v___x_2404_);
v___x_2407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2380_);
lean_ctor_set(v___x_2407_, 1, v___x_2403_);
lean_ctor_set(v___x_2407_, 2, v___x_2406_);
v___y_2395_ = v___y_2400_;
v___y_2396_ = v___x_2407_;
goto v___jp_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2419_, lean_object* v_term_2420_, lean_object* v_nesting_2421_, lean_object* v_name_2422_, lean_object* v_isPseudoKind_2423_){
_start:
{
uint8_t v_isPseudoKind_boxed_2424_; lean_object* v_res_2425_; 
v_isPseudoKind_boxed_2424_ = lean_unbox(v_isPseudoKind_2423_);
v_res_2425_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2419_, v_term_2420_, v_nesting_2421_, v_name_2422_, v_isPseudoKind_boxed_2424_);
return v_res_2425_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2426_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2427_ = lean_unsigned_to_nat(1u);
v___x_2428_ = l_Lean_Syntax_getArg(v_stx_2426_, v___x_2427_);
v___x_2429_ = l_Lean_Syntax_getArgs(v___x_2428_);
lean_dec(v___x_2428_);
v___x_2430_ = lean_array_get_size(v___x_2429_);
lean_dec_ref(v___x_2429_);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = lean_nat_dec_eq(v___x_2430_, v___x_2431_);
if (v___x_2432_ == 0)
{
uint8_t v___x_2433_; 
v___x_2433_ = 1;
return v___x_2433_;
}
else
{
uint8_t v___x_2434_; 
v___x_2434_ = 0;
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2435_);
lean_dec(v_stx_2435_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2438_){
_start:
{
uint8_t v___x_2439_; 
v___x_2439_ = l_Lean_Syntax_isAntiquot(v_stx_2438_);
if (v___x_2439_ == 0)
{
return v_stx_2438_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2440_ = lean_unsigned_to_nat(1u);
v___x_2441_ = l_Lean_Syntax_getArg(v_stx_2438_, v___x_2440_);
v___x_2442_ = l_Lean_Syntax_getArgs(v___x_2441_);
lean_dec(v___x_2441_);
v___x_2443_ = lean_array_pop(v___x_2442_);
v___x_2444_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2445_ = lean_box(2);
v___x_2446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v___x_2444_);
lean_ctor_set(v___x_2446_, 2, v___x_2443_);
v___x_2447_ = l_Lean_Syntax_setArg(v_stx_2438_, v___x_2440_, v___x_2446_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2448_){
_start:
{
lean_object* v___y_2450_; uint8_t v___x_2461_; 
v___x_2461_ = l_Lean_Syntax_isAntiquot(v_stx_2448_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_unsigned_to_nat(3u);
v___x_2463_ = l_Lean_Syntax_getArg(v_stx_2448_, v___x_2462_);
v___y_2450_ = v___x_2463_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_unsigned_to_nat(2u);
v___x_2465_ = l_Lean_Syntax_getArg(v_stx_2448_, v___x_2464_);
v___y_2450_ = v___x_2465_;
goto v___jp_2449_;
}
v___jp_2449_:
{
uint8_t v___x_2451_; 
v___x_2451_ = l_Lean_Syntax_isIdent(v___y_2450_);
if (v___x_2451_ == 0)
{
uint8_t v___x_2452_; 
v___x_2452_ = l_Lean_Syntax_isAtom(v___y_2450_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = l_Lean_Syntax_getArg(v___y_2450_, v___x_2453_);
lean_dec(v___y_2450_);
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2455_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2456_ = lean_unsigned_to_nat(1u);
v___x_2457_ = lean_mk_empty_array_with_capacity(v___x_2456_);
v___x_2458_ = lean_array_push(v___x_2457_, v___y_2450_);
v___x_2459_ = lean_box(2);
v___x_2460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v___x_2455_);
lean_ctor_set(v___x_2460_, 2, v___x_2458_);
return v___x_2460_;
}
}
else
{
return v___y_2450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2466_);
lean_dec(v_stx_2466_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2468_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 1)
{
lean_object* v_kind_2469_; 
v_kind_2469_ = lean_ctor_get(v_x_2468_, 1);
if (lean_obj_tag(v_kind_2469_) == 1)
{
lean_object* v_pre_2470_; lean_object* v_str_2471_; 
v_pre_2470_ = lean_ctor_get(v_kind_2469_, 0);
v_str_2471_ = lean_ctor_get(v_kind_2469_, 1);
if (lean_obj_tag(v_pre_2470_) == 1)
{
lean_object* v_pre_2477_; lean_object* v_str_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_pre_2477_ = lean_ctor_get(v_pre_2470_, 0);
v_str_2478_ = lean_ctor_get(v_pre_2470_, 1);
v___x_2479_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2480_ = lean_string_dec_eq(v_str_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2482_ = lean_string_dec_eq(v_str_2471_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_box(0);
return v___x_2483_;
}
else
{
goto v___jp_2472_;
}
}
else
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2485_ = lean_string_dec_eq(v_str_2471_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_box(0);
return v___x_2486_;
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_box(v___x_2485_);
lean_inc(v_pre_2477_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_pre_2477_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
return v___x_2489_;
}
}
}
else
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2491_ = lean_string_dec_eq(v_str_2471_, v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_box(0);
return v___x_2492_;
}
else
{
goto v___jp_2472_;
}
}
v___jp_2472_:
{
uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = 0;
v___x_2474_ = lean_box(v___x_2473_);
lean_inc(v_pre_2470_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v_pre_2470_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
else
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_box(0);
return v___x_2493_;
}
}
else
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_box(0);
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2495_);
lean_dec(v_x_2495_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2497_, size_t v_i_2498_, size_t v_stop_2499_, lean_object* v_b_2500_){
_start:
{
lean_object* v___y_2502_; uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_eq(v_i_2498_, v_stop_2499_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_array_uget_borrowed(v_as_2497_, v_i_2498_);
v___x_2508_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
v___y_2502_ = v_b_2500_;
goto v___jp_2501_;
}
else
{
lean_object* v_val_2509_; lean_object* v___x_2510_; 
v_val_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = lean_array_push(v_b_2500_, v_val_2509_);
v___y_2502_ = v___x_2510_;
goto v___jp_2501_;
}
}
else
{
return v_b_2500_;
}
v___jp_2501_:
{
size_t v___x_2503_; size_t v___x_2504_; 
v___x_2503_ = ((size_t)1ULL);
v___x_2504_ = lean_usize_add(v_i_2498_, v___x_2503_);
v_i_2498_ = v___x_2504_;
v_b_2500_ = v___y_2502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2511_, lean_object* v_i_2512_, lean_object* v_stop_2513_, lean_object* v_b_2514_){
_start:
{
size_t v_i_boxed_2515_; size_t v_stop_boxed_2516_; lean_object* v_res_2517_; 
v_i_boxed_2515_ = lean_unbox_usize(v_i_2512_);
lean_dec(v_i_2512_);
v_stop_boxed_2516_ = lean_unbox_usize(v_stop_2513_);
lean_dec(v_stop_2513_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2511_, v_i_boxed_2515_, v_stop_boxed_2516_, v_b_2514_);
lean_dec_ref(v_as_2511_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2520_, lean_object* v_start_2521_, lean_object* v_stop_2522_){
_start:
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2524_ = lean_nat_dec_lt(v_start_2521_, v_stop_2522_);
if (v___x_2524_ == 0)
{
return v___x_2523_;
}
else
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = lean_array_get_size(v_as_2520_);
v___x_2526_ = lean_nat_dec_le(v_stop_2522_, v___x_2525_);
if (v___x_2526_ == 0)
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_nat_dec_lt(v_start_2521_, v___x_2525_);
if (v___x_2527_ == 0)
{
return v___x_2523_;
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_usize_of_nat(v_start_2521_);
v___x_2529_ = lean_usize_of_nat(v___x_2525_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2520_, v___x_2528_, v___x_2529_, v___x_2523_);
return v___x_2530_;
}
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_usize_of_nat(v_start_2521_);
v___x_2532_ = lean_usize_of_nat(v_stop_2522_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2520_, v___x_2531_, v___x_2532_, v___x_2523_);
return v___x_2533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2534_, lean_object* v_start_2535_, lean_object* v_stop_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2534_, v_start_2535_, v_stop_2536_);
lean_dec(v_stop_2536_);
lean_dec(v_start_2535_);
lean_dec_ref(v_as_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2538_){
_start:
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2538_);
v___x_2540_ = l_Lean_Syntax_isOfKind(v_stx_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2538_);
lean_dec(v_stx_2538_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_box(0);
return v___x_2542_;
}
else
{
lean_object* v_val_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v_val_2543_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_val_2543_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2545_, 0, v_val_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
return v___x_2545_;
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2546_ = l_Lean_Syntax_getArgs(v_stx_2538_);
lean_dec(v_stx_2538_);
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_array_get_size(v___x_2546_);
v___x_2549_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2546_, v___x_2547_, v___x_2548_);
lean_dec_ref(v___x_2546_);
v___x_2550_ = lean_array_to_list(v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2552_){
_start:
{
if (lean_obj_tag(v_x_2552_) == 1)
{
lean_object* v_kind_2553_; 
v_kind_2553_ = lean_ctor_get(v_x_2552_, 1);
if (lean_obj_tag(v_kind_2553_) == 1)
{
lean_object* v_pre_2554_; lean_object* v_str_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_pre_2554_ = lean_ctor_get(v_kind_2553_, 0);
v_str_2555_ = lean_ctor_get(v_kind_2553_, 1);
v___x_2556_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2557_ = lean_string_dec_eq(v_str_2555_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
else
{
lean_object* v___x_2559_; 
lean_inc(v_pre_2554_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_pre_2554_);
return v___x_2559_;
}
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_box(0);
return v___x_2560_;
}
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_box(0);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2562_);
lean_dec(v_x_2562_);
return v_res_2563_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2564_);
if (lean_obj_tag(v___x_2565_) == 0)
{
uint8_t v___x_2566_; 
v___x_2566_ = 0;
return v___x_2566_;
}
else
{
uint8_t v___x_2567_; 
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = 1;
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2568_){
_start:
{
uint8_t v_res_2569_; lean_object* v_r_2570_; 
v_res_2569_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2568_);
lean_dec(v_stx_2568_);
v_r_2570_ = lean_box(v_res_2569_);
return v_r_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2571_){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = lean_unsigned_to_nat(3u);
v___x_2573_ = l_Lean_Syntax_getArg(v_stx_2571_, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_getArgs(v___x_2573_);
lean_dec(v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2575_);
lean_dec(v_stx_2575_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_unsigned_to_nat(1u);
v___x_2580_ = l_Lean_Syntax_getArg(v_stx_2577_, v___x_2579_);
return v___x_2580_;
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = lean_unsigned_to_nat(5u);
v___x_2582_ = l_Lean_Syntax_getArg(v_stx_2577_, v___x_2581_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2583_);
lean_dec(v_stx_2583_);
return v_res_2584_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2590_ = l_Lean_mkAtom(v___x_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2593_ = l_Lean_mkAtom(v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2594_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2595_ = lean_unsigned_to_nat(6u);
v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2595_);
v___x_2597_ = lean_array_push(v___x_2596_, v___x_2594_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2598_, lean_object* v_contents_2599_, lean_object* v_suffix_2600_, lean_object* v_nesting_2601_){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_nesting_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2602_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2603_ = lean_mk_array(v_nesting_2601_, v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2605_ = lean_box(2);
v_nesting_2606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2606_, 0, v___x_2605_);
lean_ctor_set(v_nesting_2606_, 1, v___x_2604_);
lean_ctor_set(v_nesting_2606_, 2, v___x_2603_);
v___x_2607_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2608_ = l_Lean_Name_append(v_kind_2598_, v___x_2607_);
v___x_2609_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2605_);
lean_ctor_set(v___x_2610_, 1, v___x_2604_);
lean_ctor_set(v___x_2610_, 2, v_contents_2599_);
v___x_2611_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2612_ = l_Lean_mkAtom(v_suffix_2600_);
v___x_2613_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2614_ = lean_array_push(v___x_2613_, v_nesting_2606_);
v___x_2615_ = lean_array_push(v___x_2614_, v___x_2609_);
v___x_2616_ = lean_array_push(v___x_2615_, v___x_2610_);
v___x_2617_ = lean_array_push(v___x_2616_, v___x_2611_);
v___x_2618_ = lean_array_push(v___x_2617_, v___x_2612_);
v___x_2619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2605_);
lean_ctor_set(v___x_2619_, 1, v___x_2608_);
lean_ctor_set(v___x_2619_, 2, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2621_){
_start:
{
if (lean_obj_tag(v_x_2621_) == 1)
{
lean_object* v_kind_2622_; 
v_kind_2622_ = lean_ctor_get(v_x_2621_, 1);
if (lean_obj_tag(v_kind_2622_) == 1)
{
lean_object* v_pre_2623_; lean_object* v_str_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_pre_2623_ = lean_ctor_get(v_kind_2622_, 0);
v_str_2624_ = lean_ctor_get(v_kind_2622_, 1);
v___x_2625_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2626_ = lean_string_dec_eq(v_str_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_box(0);
return v___x_2627_;
}
else
{
lean_object* v___x_2628_; 
lean_inc(v_pre_2623_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_pre_2623_);
return v___x_2628_;
}
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_box(0);
return v___x_2629_;
}
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_box(0);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2631_);
lean_dec(v_x_2631_);
return v_res_2632_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2633_);
if (lean_obj_tag(v___x_2634_) == 0)
{
uint8_t v___x_2635_; 
v___x_2635_ = 0;
return v___x_2635_;
}
else
{
uint8_t v___x_2636_; 
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = 1;
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2637_);
lean_dec(v_stx_2637_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = l_Lean_Syntax_getArg(v_stx_2640_, v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2643_);
lean_dec(v_stx_2643_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2647_, lean_object* v_inner_2648_, lean_object* v_suffix_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2650_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2651_ = l_Lean_Name_append(v_kind_2647_, v___x_2650_);
v___x_2652_ = l_Lean_mkAtom(v_suffix_2649_);
v___x_2653_ = lean_unsigned_to_nat(2u);
v___x_2654_ = lean_mk_empty_array_with_capacity(v___x_2653_);
v___x_2655_ = lean_array_push(v___x_2654_, v_inner_2648_);
v___x_2656_ = lean_array_push(v___x_2655_, v___x_2652_);
v___x_2657_ = lean_box(2);
v___x_2658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2651_);
lean_ctor_set(v___x_2658_, 2, v___x_2656_);
return v___x_2658_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2662_){
_start:
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2664_ = l_Lean_Syntax_isOfKind(v_stx_2662_, v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2665_){
_start:
{
uint8_t v_res_2666_; lean_object* v_r_2667_; 
v_res_2666_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2665_);
v_r_2667_ = lean_box(v_res_2666_);
return v_r_2667_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2668_){
_start:
{
uint8_t v___y_2670_; uint8_t v___x_2673_; 
v___x_2673_ = l_Lean_Syntax_isAntiquot(v_stx_2668_);
if (v___x_2673_ == 0)
{
uint8_t v___x_2674_; 
v___x_2674_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2668_);
v___y_2670_ = v___x_2674_;
goto v___jp_2669_;
}
else
{
v___y_2670_ = v___x_2673_;
goto v___jp_2669_;
}
v___jp_2669_:
{
if (v___y_2670_ == 0)
{
uint8_t v___x_2671_; 
v___x_2671_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2668_);
if (v___x_2671_ == 0)
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2668_);
return v___x_2672_;
}
else
{
lean_dec(v_stx_2668_);
return v___x_2671_;
}
}
else
{
lean_dec(v_stx_2668_);
return v___y_2670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2675_){
_start:
{
uint8_t v_res_2676_; lean_object* v_r_2677_; 
v_res_2676_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2675_);
v_r_2677_ = lean_box(v_res_2676_);
return v_r_2677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2681_, lean_object* v_stx_2682_, lean_object* v_visit_2683_, lean_object* v_stack_2684_, lean_object* v_accept_2685_, lean_object* v_a_2686_, lean_object* v_b_2687_){
_start:
{
lean_object* v_a_2689_; uint8_t v___x_2693_; 
v___x_2693_ = lean_nat_dec_lt(v_a_2686_, v_upperBound_2681_);
if (v___x_2693_ == 0)
{
lean_dec(v_a_2686_);
lean_dec_ref(v_accept_2685_);
lean_dec(v_stack_2684_);
lean_dec_ref(v_visit_2683_);
lean_dec(v_stx_2682_);
lean_inc_ref(v_b_2687_);
return v_b_2687_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2696_ = l_Lean_Syntax_getArg(v_stx_2682_, v_a_2686_);
lean_inc_ref(v_visit_2683_);
lean_inc(v___x_2696_);
v___x_2697_ = lean_apply_1(v_visit_2683_, v___x_2696_);
v___x_2698_ = lean_unbox(v___x_2697_);
if (v___x_2698_ == 0)
{
lean_dec(v___x_2696_);
v_a_2689_ = v___x_2695_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_inc(v_a_2686_);
lean_inc(v_stx_2682_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_stx_2682_);
lean_ctor_set(v___x_2699_, 1, v_a_2686_);
lean_inc(v_stack_2684_);
v___x_2700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v_stack_2684_);
lean_inc_ref(v_accept_2685_);
lean_inc_ref(v_visit_2683_);
v___x_2701_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2683_, v_accept_2685_, v___x_2700_, v___x_2696_);
if (lean_obj_tag(v___x_2701_) == 1)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec(v_a_2686_);
lean_dec_ref(v_accept_2685_);
lean_dec(v_stack_2684_);
lean_dec_ref(v_visit_2683_);
lean_dec(v_stx_2682_);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2694_);
return v___x_2703_;
}
else
{
lean_dec(v___x_2701_);
v_a_2689_ = v___x_2695_;
goto v___jp_2688_;
}
}
}
v___jp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_unsigned_to_nat(1u);
v___x_2691_ = lean_nat_add(v_a_2686_, v___x_2690_);
lean_dec(v_a_2686_);
v_a_2686_ = v___x_2691_;
v_b_2687_ = v_a_2689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2704_, lean_object* v_accept_2705_, lean_object* v_stack_2706_, lean_object* v_stx_2707_){
_start:
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
lean_inc_ref(v_accept_2705_);
lean_inc(v_stx_2707_);
v___x_2708_ = lean_apply_1(v_accept_2705_, v_stx_2707_);
v___x_2709_ = lean_unbox(v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_fst_2715_; 
v___x_2710_ = l_Lean_Syntax_getNumArgs(v_stx_2707_);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_box(0);
v___x_2713_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2710_, v_stx_2707_, v_visit_2704_, v_stack_2706_, v_accept_2705_, v___x_2711_, v___x_2713_);
lean_dec(v___x_2710_);
v_fst_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_fst_2715_);
lean_dec_ref(v___x_2714_);
if (lean_obj_tag(v_fst_2715_) == 0)
{
return v___x_2712_;
}
else
{
lean_object* v_val_2716_; 
v_val_2716_ = lean_ctor_get(v_fst_2715_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v_fst_2715_, 1);
return v_val_2716_;
}
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref(v_accept_2705_);
lean_dec_ref(v_visit_2704_);
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_stx_2707_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_stack_2706_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2721_, lean_object* v_stx_2722_, lean_object* v_visit_2723_, lean_object* v_stack_2724_, lean_object* v_accept_2725_, lean_object* v_a_2726_, lean_object* v_b_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2721_, v_stx_2722_, v_visit_2723_, v_stack_2724_, v_accept_2725_, v_a_2726_, v_b_2727_);
lean_dec_ref(v_b_2727_);
lean_dec(v_upperBound_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2729_, lean_object* v_stx_2730_, lean_object* v_visit_2731_, lean_object* v_stack_2732_, lean_object* v_accept_2733_, lean_object* v_inst_2734_, lean_object* v_R_2735_, lean_object* v_a_2736_, lean_object* v_b_2737_, lean_object* v_c_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2729_, v_stx_2730_, v_visit_2731_, v_stack_2732_, v_accept_2733_, v_a_2736_, v_b_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2740_, lean_object* v_stx_2741_, lean_object* v_visit_2742_, lean_object* v_stack_2743_, lean_object* v_accept_2744_, lean_object* v_inst_2745_, lean_object* v_R_2746_, lean_object* v_a_2747_, lean_object* v_b_2748_, lean_object* v_c_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2740_, v_stx_2741_, v_visit_2742_, v_stack_2743_, v_accept_2744_, v_inst_2745_, v_R_2746_, v_a_2747_, v_b_2748_, v_c_2749_);
lean_dec_ref(v_b_2748_);
lean_dec(v_upperBound_2740_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2751_, lean_object* v_visit_2752_, lean_object* v_accept_2753_){
_start:
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
lean_inc_ref(v_visit_2752_);
lean_inc(v_root_2751_);
v___x_2754_ = lean_apply_1(v_visit_2752_, v_root_2751_);
v___x_2755_ = lean_unbox(v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref(v_accept_2753_);
lean_dec_ref(v_visit_2752_);
lean_dec(v_root_2751_);
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2752_, v_accept_2753_, v___x_2757_, v_root_2751_);
return v___x_2758_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2759_, lean_object* v_x_2760_, lean_object* v_p_2761_){
_start:
{
if (lean_obj_tag(v_p_2761_) == 0)
{
lean_dec_ref(v_x_2760_);
return v___x_2759_;
}
else
{
lean_object* v_fst_2762_; lean_object* v_val_2763_; uint8_t v___x_2764_; 
v_fst_2762_ = lean_ctor_get(v_x_2760_, 0);
lean_inc(v_fst_2762_);
lean_dec_ref(v_x_2760_);
v_val_2763_ = lean_ctor_get(v_p_2761_, 0);
v___x_2764_ = l_Lean_Syntax_isOfKind(v_fst_2762_, v_val_2763_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2765_, lean_object* v_x_2766_, lean_object* v_p_2767_){
_start:
{
uint8_t v___x_123__boxed_2768_; uint8_t v_res_2769_; lean_object* v_r_2770_; 
v___x_123__boxed_2768_ = lean_unbox(v___x_2765_);
v_res_2769_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2768_, v_x_2766_, v_p_2767_);
lean_dec(v_p_2767_);
v_r_2770_ = lean_box(v_res_2769_);
return v_r_2770_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2771_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
uint8_t v___x_2772_; 
v___x_2772_ = 1;
return v___x_2772_;
}
else
{
lean_object* v_head_2773_; uint8_t v___x_2774_; 
v_head_2773_ = lean_ctor_get(v_x_2771_, 0);
v___x_2774_ = lean_unbox(v_head_2773_);
if (v___x_2774_ == 0)
{
uint8_t v___x_2775_; 
v___x_2775_ = lean_unbox(v_head_2773_);
return v___x_2775_;
}
else
{
lean_object* v_tail_2776_; 
v_tail_2776_ = lean_ctor_get(v_x_2771_, 1);
v_x_2771_ = v_tail_2776_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2778_){
_start:
{
uint8_t v_res_2779_; lean_object* v_r_2780_; 
v_res_2779_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2778_);
lean_dec(v_x_2778_);
v_r_2780_ = lean_box(v_res_2779_);
return v_r_2780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2783_, lean_object* v_pattern_2784_){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2785_ = l_List_lengthTR___redArg(v_pattern_2784_);
v___x_2786_ = l_List_lengthTR___redArg(v_stack_2783_);
v___x_2787_ = lean_nat_dec_le(v___x_2785_, v___x_2786_);
lean_dec(v___x_2786_);
lean_dec(v___x_2785_);
if (v___x_2787_ == 0)
{
lean_dec(v_pattern_2784_);
lean_dec(v_stack_2783_);
return v___x_2787_;
}
else
{
lean_object* v___x_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2788_ = lean_box(v___x_2787_);
v___f_2789_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2789_, 0, v___x_2788_);
v___x_2790_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2791_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2789_, v_stack_2783_, v_pattern_2784_, v___x_2790_);
v___x_2792_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2791_);
lean_dec(v___x_2791_);
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2793_, lean_object* v_pattern_2794_){
_start:
{
uint8_t v_res_2795_; lean_object* v_r_2796_; 
v_res_2795_ = l_Lean_Syntax_Stack_matches(v_stack_2793_, v_pattern_2794_);
v_r_2796_ = lean_box(v_res_2795_);
return v_r_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2797_, lean_object* v_trailing_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2797_);
if (lean_obj_tag(v___x_2799_) == 1)
{
lean_object* v_val_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2835_; 
v_val_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2835_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_val_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2835_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
if (lean_obj_tag(v_val_2800_) == 0)
{
lean_object* v_trailing_2804_; lean_object* v_leading_2805_; lean_object* v_pos_2806_; lean_object* v_endPos_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2833_; 
v_trailing_2804_ = lean_ctor_get(v_val_2800_, 2);
v_leading_2805_ = lean_ctor_get(v_val_2800_, 0);
v_pos_2806_ = lean_ctor_get(v_val_2800_, 1);
v_endPos_2807_ = lean_ctor_get(v_val_2800_, 3);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_val_2800_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2809_ = v_val_2800_;
v_isShared_2810_ = v_isSharedCheck_2833_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_endPos_2807_);
lean_inc(v_trailing_2804_);
lean_inc(v_pos_2806_);
lean_inc(v_leading_2805_);
lean_dec(v_val_2800_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2833_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v_str_2811_; lean_object* v_startPos_2812_; lean_object* v_stopPos_2813_; lean_object* v_startPos_2814_; lean_object* v_stopPos_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2831_; 
v_str_2811_ = lean_ctor_get(v_trailing_2804_, 0);
lean_inc_ref(v_str_2811_);
v_startPos_2812_ = lean_ctor_get(v_trailing_2804_, 1);
lean_inc(v_startPos_2812_);
v_stopPos_2813_ = lean_ctor_get(v_trailing_2804_, 2);
lean_inc(v_stopPos_2813_);
lean_dec_ref(v_trailing_2804_);
v_startPos_2814_ = lean_ctor_get(v_trailing_2798_, 1);
v_stopPos_2815_ = lean_ctor_get(v_trailing_2798_, 2);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_trailing_2798_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v_trailing_2798_, 0);
lean_dec(v_unused_2832_);
v___x_2817_ = v_trailing_2798_;
v_isShared_2818_ = v_isSharedCheck_2831_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_stopPos_2815_);
lean_inc(v_startPos_2814_);
lean_dec(v_trailing_2798_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2831_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
uint8_t v_decide_2819_; 
v_decide_2819_ = lean_nat_dec_eq(v_stopPos_2813_, v_startPos_2814_);
lean_dec(v_startPos_2814_);
lean_dec(v_stopPos_2813_);
if (v_decide_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_del_object(v___x_2817_);
lean_dec(v_stopPos_2815_);
lean_dec(v_startPos_2812_);
lean_dec_ref(v_str_2811_);
lean_del_object(v___x_2809_);
lean_dec(v_endPos_2807_);
lean_dec(v_pos_2806_);
lean_dec_ref(v_leading_2805_);
lean_del_object(v___x_2802_);
lean_dec(v_stx_2797_);
v___x_2820_ = lean_box(0);
return v___x_2820_;
}
else
{
lean_object* v_trailing_2822_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v_startPos_2812_);
lean_ctor_set(v___x_2817_, 0, v_str_2811_);
v_trailing_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_str_2811_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_startPos_2812_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_stopPos_2815_);
v_trailing_2822_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 2, v_trailing_2822_);
v___x_2824_ = v___x_2809_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_leading_2805_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_pos_2806_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_trailing_2822_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_endPos_2807_);
v___x_2824_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = l_Lean_Syntax_setTailInfo(v_stx_2797_, v___x_2824_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2825_);
v___x_2827_ = v___x_2802_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2834_; 
lean_del_object(v___x_2802_);
lean_dec(v_val_2800_);
lean_dec_ref(v_trailing_2798_);
lean_dec(v_stx_2797_);
v___x_2834_ = lean_box(0);
return v___x_2834_;
}
}
}
else
{
lean_object* v___x_2836_; 
lean_dec(v___x_2799_);
lean_dec_ref(v_trailing_2798_);
lean_dec(v_stx_2797_);
v___x_2836_ = lean_box(0);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2837_, lean_object* v_trailing_2838_){
_start:
{
lean_object* v___x_2839_; 
lean_inc(v_stx_2837_);
v___x_2839_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2837_, v_trailing_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
return v_stx_2837_;
}
else
{
lean_object* v_val_2840_; 
lean_dec(v_stx_2837_);
v_val_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_val_2840_);
lean_dec_ref_known(v___x_2839_, 1);
return v_val_2840_;
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

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
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object* v_x_93_, lean_object* v_x_94_){
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
LEAN_EXPORT void l_Lean_Syntax_instBEqRange_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_93_ = stack[0].m_obj;
lean_object* v_x_94_ = stack[1].m_obj;
uint8_t v_res_101_;
v_res_101_ = l_Lean_Syntax_instBEqRange_beq(v_x_93_, v_x_94_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Syntax_instBEqRange_beq(v_x_102_, v_x_103_);
lean_dec_ref(v_x_103_);
lean_dec_ref(v_x_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object* v_x_108_){
_start:
{
lean_object* v_start_109_; lean_object* v_stop_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; 
v_start_109_ = lean_ctor_get(v_x_108_, 0);
v_stop_110_ = lean_ctor_get(v_x_108_, 1);
v___x_111_ = 0ULL;
v___x_112_ = l_String_instHashableRaw_hash(v_start_109_);
v___x_113_ = lean_uint64_mix_hash(v___x_111_, v___x_112_);
v___x_114_ = l_String_instHashableRaw_hash(v_stop_110_);
v___x_115_ = lean_uint64_mix_hash(v___x_113_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instHashableRange_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_108_ = stack[0].m_obj;
uint64_t v_res_116_;
v_res_116_ = l_Lean_Syntax_instHashableRange_hash(v_x_108_);
stack->m_num = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object* v_x_117_){
_start:
{
uint64_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Lean_Syntax_instHashableRange_hash(v_x_117_);
lean_dec_ref(v_x_117_);
v_r_119_ = lean_box_uint64(v_res_118_);
return v_r_119_;
}
}
uint8_t l_Lean_Syntax_Range_contains(lean_object* v_r_122_, lean_object* v_pos_123_, uint8_t v_includeStop_124_){
_start:
{
lean_object* v_start_125_; lean_object* v_stop_126_; uint8_t v___x_127_; 
v_start_125_ = lean_ctor_get(v_r_122_, 0);
v_stop_126_ = lean_ctor_get(v_r_122_, 1);
v___x_127_ = lean_nat_dec_le(v_start_125_, v_pos_123_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
if (v_includeStop_124_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_pos_123_, v___x_128_);
v___x_130_ = lean_nat_dec_le(v___x_129_, v_stop_126_);
lean_dec(v___x_129_);
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_le(v_pos_123_, v_stop_126_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_Range_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_122_ = stack[0].m_obj;
lean_object* v_pos_123_ = stack[1].m_obj;
uint8_t v_includeStop_124_ = stack[2].m_num;
uint8_t v_res_132_;
v_res_132_ = l_Lean_Syntax_Range_contains(v_r_122_, v_pos_123_, v_includeStop_124_);
stack->m_num = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object* v_r_133_, lean_object* v_pos_134_, lean_object* v_includeStop_135_){
_start:
{
uint8_t v_includeStop_boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_includeStop_boxed_136_ = lean_unbox(v_includeStop_135_);
v_res_137_ = l_Lean_Syntax_Range_contains(v_r_133_, v_pos_134_, v_includeStop_boxed_136_);
lean_dec(v_pos_134_);
lean_dec_ref(v_r_133_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
uint8_t l_Lean_Syntax_Range_includes(lean_object* v_super_139_, lean_object* v_sub_140_, uint8_t v_includeSuperStop_141_, uint8_t v_includeSubStop_142_){
_start:
{
lean_object* v_start_143_; lean_object* v_stop_144_; lean_object* v_start_145_; lean_object* v_stop_146_; uint8_t v___y_148_; uint8_t v___x_154_; uint8_t v___y_156_; 
v_start_143_ = lean_ctor_get(v_super_139_, 0);
v_stop_144_ = lean_ctor_get(v_super_139_, 1);
v_start_145_ = lean_ctor_get(v_sub_140_, 0);
v_stop_146_ = lean_ctor_get(v_sub_140_, 1);
v___x_154_ = lean_nat_dec_le(v_start_143_, v_start_145_);
if (v___x_154_ == 0)
{
return v___x_154_;
}
else
{
if (v_includeSuperStop_141_ == 0)
{
v___y_156_ = v_includeSuperStop_141_;
goto v___jp_155_;
}
else
{
if (v_includeSubStop_142_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_stop_144_, v___x_157_);
v___x_159_ = lean_nat_dec_le(v_stop_146_, v___x_158_);
lean_dec(v___x_158_);
return v___x_159_;
}
else
{
uint8_t v___x_160_; 
v___x_160_ = 0;
v___y_156_ = v___x_160_;
goto v___jp_155_;
}
}
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_le(v_stop_146_, v_stop_144_);
return v___x_149_;
}
else
{
if (v_includeSubStop_142_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v_stop_146_, v_stop_144_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_stop_146_, v___x_151_);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_stop_144_);
lean_dec(v___x_152_);
return v___x_153_;
}
}
}
v___jp_155_:
{
if (v_includeSuperStop_141_ == 0)
{
v___y_148_ = v___x_154_;
goto v___jp_147_;
}
else
{
v___y_148_ = v___y_156_;
goto v___jp_147_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_Range_includes_0interp(lean_interpreter_value* stack)
{
lean_object* v_super_139_ = stack[0].m_obj;
lean_object* v_sub_140_ = stack[1].m_obj;
uint8_t v_includeSuperStop_141_ = stack[2].m_num;
uint8_t v_includeSubStop_142_ = stack[3].m_num;
uint8_t v_res_161_;
v_res_161_ = l_Lean_Syntax_Range_includes(v_super_139_, v_sub_140_, v_includeSuperStop_141_, v_includeSubStop_142_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_162_, lean_object* v_sub_163_, lean_object* v_includeSuperStop_164_, lean_object* v_includeSubStop_165_){
_start:
{
uint8_t v_includeSuperStop_boxed_166_; uint8_t v_includeSubStop_boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_includeSuperStop_boxed_166_ = lean_unbox(v_includeSuperStop_164_);
v_includeSubStop_boxed_167_ = lean_unbox(v_includeSubStop_165_);
v_res_168_ = l_Lean_Syntax_Range_includes(v_super_162_, v_sub_163_, v_includeSuperStop_boxed_166_, v_includeSubStop_boxed_167_);
lean_dec_ref(v_sub_163_);
lean_dec_ref(v_super_162_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_170_, lean_object* v_second_171_, uint8_t v_includeFirstStop_172_, uint8_t v_includeSecondStop_173_){
_start:
{
uint8_t v___y_175_; 
if (v_includeFirstStop_172_ == 0)
{
lean_object* v_start_184_; lean_object* v_stop_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_start_184_ = lean_ctor_get(v_second_171_, 0);
v_stop_185_ = lean_ctor_get(v_first_170_, 1);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_start_184_, v___x_186_);
v___x_188_ = lean_nat_dec_le(v___x_187_, v_stop_185_);
lean_dec(v___x_187_);
v___y_175_ = v___x_188_;
goto v___jp_174_;
}
else
{
lean_object* v_start_189_; lean_object* v_stop_190_; uint8_t v___x_191_; 
v_start_189_ = lean_ctor_get(v_second_171_, 0);
v_stop_190_ = lean_ctor_get(v_first_170_, 1);
v___x_191_ = lean_nat_dec_le(v_start_189_, v_stop_190_);
v___y_175_ = v___x_191_;
goto v___jp_174_;
}
v___jp_174_:
{
if (v___y_175_ == 0)
{
return v___y_175_;
}
else
{
if (v_includeSecondStop_173_ == 0)
{
lean_object* v_start_176_; lean_object* v_stop_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_start_176_ = lean_ctor_get(v_first_170_, 0);
v_stop_177_ = lean_ctor_get(v_second_171_, 1);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_start_176_, v___x_178_);
v___x_180_ = lean_nat_dec_le(v___x_179_, v_stop_177_);
lean_dec(v___x_179_);
return v___x_180_;
}
else
{
lean_object* v_start_181_; lean_object* v_stop_182_; uint8_t v___x_183_; 
v_start_181_ = lean_ctor_get(v_first_170_, 0);
v_stop_182_ = lean_ctor_get(v_second_171_, 1);
v___x_183_ = lean_nat_dec_le(v_start_181_, v_stop_182_);
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_Range_overlaps_0interp(lean_interpreter_value* stack)
{
lean_object* v_first_170_ = stack[0].m_obj;
lean_object* v_second_171_ = stack[1].m_obj;
uint8_t v_includeFirstStop_172_ = stack[2].m_num;
uint8_t v_includeSecondStop_173_ = stack[3].m_num;
uint8_t v_res_192_;
v_res_192_ = l_Lean_Syntax_Range_overlaps(v_first_170_, v_second_171_, v_includeFirstStop_172_, v_includeSecondStop_173_);
stack->m_num = v_res_192_;
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
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_201_){
_start:
{
lean_object* v_start_202_; lean_object* v_stop_203_; lean_object* v___x_204_; 
v_start_202_ = lean_ctor_get(v_r_201_, 0);
v_stop_203_ = lean_ctor_get(v_r_201_, 1);
v___x_204_ = lean_nat_sub(v_stop_203_, v_start_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Syntax_Range_bsize(v_r_205_);
lean_dec_ref(v_r_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v_leading_209_; lean_object* v_pos_210_; lean_object* v_endPos_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_leading_209_ = lean_ctor_get(v_x_208_, 0);
v_pos_210_ = lean_ctor_get(v_x_208_, 1);
v_endPos_211_ = lean_ctor_get(v_x_208_, 3);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_x_208_, 2);
lean_dec(v_unused_219_);
v___x_213_ = v_x_208_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_endPos_211_);
lean_inc(v_pos_210_);
lean_inc(v_leading_209_);
lean_dec(v_x_208_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 2, v_trailing_207_);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_leading_209_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_pos_210_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_trailing_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_endPos_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_dec_ref(v_trailing_207_);
return v_x_208_;
}
}
}
lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_220_, lean_object* v_info_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_SourceInfo_getPos_x3f(v_info_221_, v_canonicalOnly_220_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_225_; 
v_val_224_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_222_, 1);
v___x_225_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_221_, v_canonicalOnly_220_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; 
lean_dec(v_val_224_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_235_; 
v_val_227_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_235_ == 0)
{
v___x_229_ = v___x_225_;
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_val_227_);
lean_dec(v___x_225_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_val_224_);
lean_ctor_set(v___x_231_, 1, v_val_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_231_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_SourceInfo_getRange_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_canonicalOnly_220_ = stack[0].m_num;
lean_object* v_info_221_ = stack[1].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_220_, v_info_221_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_237_, lean_object* v_info_238_){
_start:
{
uint8_t v_canonicalOnly_boxed_239_; lean_object* v_res_240_; 
v_canonicalOnly_boxed_239_ = lean_unbox(v_canonicalOnly_237_);
v_res_240_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_239_, v_info_238_);
lean_dec(v_info_238_);
return v_res_240_;
}
}
lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_241_, lean_object* v_info_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_SourceInfo_getPos_x3f(v_info_242_, v_canonicalOnly_241_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
return v___x_244_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_246_; 
v_val_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v___x_243_, 1);
v___x_246_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_242_, v_canonicalOnly_241_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; 
lean_dec(v_val_245_);
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v___x_246_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_dec(v___x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_val_245_);
lean_ctor_set(v___x_252_, 1, v_val_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
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
}
}
LEAN_EXPORT void l_Lean_SourceInfo_getRangeWithTrailing_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_canonicalOnly_241_ = stack[0].m_num;
lean_object* v_info_242_ = stack[1].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_241_, v_info_242_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_258_, lean_object* v_info_259_){
_start:
{
uint8_t v_canonicalOnly_boxed_260_; lean_object* v_res_261_; 
v_canonicalOnly_boxed_260_ = lean_unbox(v_canonicalOnly_258_);
v_res_261_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_260_, v_info_259_);
lean_dec(v_info_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_262_){
_start:
{
switch(lean_obj_tag(v_x_262_))
{
case 0:
{
lean_object* v_pos_263_; lean_object* v_endPos_264_; uint8_t v___x_265_; lean_object* v___x_266_; 
v_pos_263_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_pos_263_);
v_endPos_264_ = lean_ctor_get(v_x_262_, 3);
lean_inc(v_endPos_264_);
lean_dec_ref_known(v_x_262_, 4);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_266_, 0, v_pos_263_);
lean_ctor_set(v___x_266_, 1, v_endPos_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*2, v___x_265_);
return v___x_266_;
}
case 1:
{
lean_object* v_pos_267_; lean_object* v_endPos_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_pos_267_ = lean_ctor_get(v_x_262_, 0);
v_endPos_268_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v_x_262_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_endPos_268_);
lean_inc(v_pos_267_);
lean_dec(v_x_262_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
uint8_t v___x_272_; lean_object* v___x_274_; 
v___x_272_ = 0;
if (v_isShared_271_ == 0)
{
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_pos_267_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_endPos_268_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*2, v___x_272_);
return v___x_274_;
}
}
}
default: 
{
return v_x_262_;
}
}
}
}
uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
switch(lean_obj_tag(v_x_277_))
{
case 0:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v_leading_279_; lean_object* v_pos_280_; lean_object* v_trailing_281_; lean_object* v_endPos_282_; lean_object* v_leading_283_; lean_object* v_pos_284_; lean_object* v_trailing_285_; lean_object* v_endPos_286_; uint8_t v___x_287_; 
v_leading_279_ = lean_ctor_get(v_x_277_, 0);
lean_inc_ref(v_leading_279_);
v_pos_280_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_pos_280_);
v_trailing_281_ = lean_ctor_get(v_x_277_, 2);
lean_inc_ref(v_trailing_281_);
v_endPos_282_ = lean_ctor_get(v_x_277_, 3);
lean_inc(v_endPos_282_);
lean_dec_ref_known(v_x_277_, 4);
v_leading_283_ = lean_ctor_get(v_x_278_, 0);
lean_inc_ref(v_leading_283_);
v_pos_284_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_pos_284_);
v_trailing_285_ = lean_ctor_get(v_x_278_, 2);
lean_inc_ref(v_trailing_285_);
v_endPos_286_ = lean_ctor_get(v_x_278_, 3);
lean_inc(v_endPos_286_);
lean_dec_ref_known(v_x_278_, 4);
v___x_287_ = l_Substring_Raw_beq(v_leading_279_, v_leading_283_);
if (v___x_287_ == 0)
{
lean_dec(v_endPos_286_);
lean_dec_ref(v_trailing_285_);
lean_dec(v_pos_284_);
lean_dec(v_endPos_282_);
lean_dec_ref(v_trailing_281_);
lean_dec(v_pos_280_);
return v___x_287_;
}
else
{
uint8_t v_decide_288_; 
v_decide_288_ = lean_nat_dec_eq(v_pos_280_, v_pos_284_);
lean_dec(v_pos_284_);
lean_dec(v_pos_280_);
if (v_decide_288_ == 0)
{
lean_dec(v_endPos_286_);
lean_dec_ref(v_trailing_285_);
lean_dec(v_endPos_282_);
lean_dec_ref(v_trailing_281_);
return v_decide_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = l_Substring_Raw_beq(v_trailing_281_, v_trailing_285_);
if (v___x_289_ == 0)
{
lean_dec(v_endPos_286_);
lean_dec(v_endPos_282_);
return v___x_289_;
}
else
{
uint8_t v_decide_290_; 
v_decide_290_ = lean_nat_dec_eq(v_endPos_282_, v_endPos_286_);
lean_dec(v_endPos_286_);
lean_dec(v_endPos_282_);
return v_decide_290_;
}
}
}
}
else
{
uint8_t v___x_291_; 
lean_dec_ref_known(v_x_277_, 4);
lean_dec(v_x_278_);
v___x_291_ = 0;
return v___x_291_;
}
}
case 1:
{
if (lean_obj_tag(v_x_278_) == 1)
{
lean_object* v_pos_292_; lean_object* v_endPos_293_; uint8_t v_canonical_294_; lean_object* v_pos_295_; lean_object* v_endPos_296_; uint8_t v_canonical_297_; uint8_t v_decide_298_; 
v_pos_292_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_pos_292_);
v_endPos_293_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_endPos_293_);
v_canonical_294_ = lean_ctor_get_uint8(v_x_277_, sizeof(void*)*2);
lean_dec_ref_known(v_x_277_, 2);
v_pos_295_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_pos_295_);
v_endPos_296_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_endPos_296_);
v_canonical_297_ = lean_ctor_get_uint8(v_x_278_, sizeof(void*)*2);
lean_dec_ref_known(v_x_278_, 2);
v_decide_298_ = lean_nat_dec_eq(v_pos_292_, v_pos_295_);
lean_dec(v_pos_295_);
lean_dec(v_pos_292_);
if (v_decide_298_ == 0)
{
lean_dec(v_endPos_296_);
lean_dec(v_endPos_293_);
return v_decide_298_;
}
else
{
uint8_t v_decide_299_; 
v_decide_299_ = lean_nat_dec_eq(v_endPos_293_, v_endPos_296_);
lean_dec(v_endPos_296_);
lean_dec(v_endPos_293_);
if (v_decide_299_ == 0)
{
return v_decide_299_;
}
else
{
if (v_canonical_297_ == 0)
{
if (v_canonical_294_ == 0)
{
return v_decide_299_;
}
else
{
return v_canonical_297_;
}
}
else
{
return v_canonical_294_;
}
}
}
}
else
{
uint8_t v___x_300_; 
lean_dec_ref_known(v_x_277_, 2);
lean_dec(v_x_278_);
v___x_300_ = 0;
return v___x_300_;
}
}
default: 
{
if (lean_obj_tag(v_x_278_) == 2)
{
uint8_t v___x_301_; 
v___x_301_ = 1;
return v___x_301_;
}
else
{
uint8_t v___x_302_; 
lean_dec(v_x_278_);
v___x_302_ = 0;
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqSourceInfo__lean_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_277_ = stack[0].m_obj;
lean_object* v_x_278_ = stack[1].m_obj;
uint8_t v_res_303_;
v_res_303_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_277_, v_x_278_);
stack->m_num = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_304_, v_x_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
lean_object* l_Lean_unreachIsNodeMissing___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Lean_unreachIsNodeMissing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_311_;
v_res_311_ = l_Lean_unreachIsNodeMissing___redArg();
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg___boxed(lean_object* v___dummy_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_unreachIsNodeMissing___redArg();
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_314_, lean_object* v_a_315_){
_start:
{
lean_internal_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeAtom___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Lean_unreachIsNodeAtom___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_317_;
v_res_317_ = l_Lean_unreachIsNodeAtom___redArg();
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___redArg___boxed(lean_object* v___dummy_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_unreachIsNodeAtom___redArg();
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_320_, lean_object* v_info_321_, lean_object* v_val_322_, lean_object* v_a_323_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_324_, lean_object* v_info_325_, lean_object* v_val_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_324_, v_info_325_, v_val_326_, v_a_327_);
lean_dec_ref(v_val_326_);
lean_dec(v_info_325_);
return v_res_328_;
}
}
lean_object* l_Lean_unreachIsNodeIdent___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Lean_unreachIsNodeIdent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_330_;
v_res_330_ = l_Lean_unreachIsNodeIdent___redArg();
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg___boxed(lean_object* v___dummy_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_unreachIsNodeIdent___redArg();
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_333_, lean_object* v_info_334_, lean_object* v_rawVal_335_, lean_object* v_val_336_, lean_object* v_preresolved_337_, lean_object* v_a_338_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_339_, lean_object* v_info_340_, lean_object* v_rawVal_341_, lean_object* v_val_342_, lean_object* v_preresolved_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_339_, v_info_340_, v_rawVal_341_, v_val_342_, v_preresolved_343_, v_a_344_);
lean_dec(v_preresolved_343_);
lean_dec(v_val_342_);
lean_dec_ref(v_rawVal_341_);
lean_dec(v_info_340_);
return v_res_345_;
}
}
uint8_t l_Lean_isLitKind(lean_object* v_k_361_){
_start:
{
uint8_t v___y_363_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_371_ = lean_name_eq(v_k_361_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_373_ = lean_name_eq(v_k_361_, v___x_372_);
v___y_363_ = v___x_373_;
goto v___jp_362_;
}
else
{
v___y_363_ = v___x_371_;
goto v___jp_362_;
}
v___jp_362_:
{
if (v___y_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_365_ = lean_name_eq(v_k_361_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_367_ = lean_name_eq(v_k_361_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_369_ = lean_name_eq(v_k_361_, v___x_368_);
return v___x_369_;
}
else
{
return v___x_367_;
}
}
else
{
return v___x_365_;
}
}
else
{
return v___y_363_;
}
}
}
}
LEAN_EXPORT void l_Lean_isLitKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_361_ = stack[0].m_obj;
uint8_t v_res_374_;
v_res_374_ = l_Lean_isLitKind(v_k_361_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Lean_isLitKind(v_k_375_);
lean_dec(v_k_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_378_){
_start:
{
lean_object* v_kind_379_; 
v_kind_379_ = lean_ctor_get(v_n_378_, 1);
lean_inc(v_kind_379_);
return v_kind_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_SyntaxNode_getKind(v_n_380_);
lean_dec(v_n_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_382_, lean_object* v_fn_383_){
_start:
{
lean_object* v_args_384_; lean_object* v___x_385_; 
v_args_384_ = lean_ctor_get(v_n_382_, 2);
lean_inc_ref(v_args_384_);
lean_dec(v_n_382_);
v___x_385_ = lean_apply_1(v_fn_383_, v_args_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_386_, lean_object* v_n_387_, lean_object* v_fn_388_){
_start:
{
lean_object* v_args_389_; lean_object* v___x_390_; 
v_args_389_ = lean_ctor_get(v_n_387_, 2);
lean_inc_ref(v_args_389_);
lean_dec(v_n_387_);
v___x_390_ = lean_apply_1(v_fn_388_, v_args_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_391_){
_start:
{
lean_object* v_args_392_; lean_object* v___x_393_; 
v_args_392_ = lean_ctor_get(v_n_391_, 2);
v___x_393_ = lean_array_get_size(v_args_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_SyntaxNode_getNumArgs(v_n_394_);
lean_dec(v_n_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_396_, lean_object* v_i_397_){
_start:
{
lean_object* v_args_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_args_398_ = lean_ctor_get(v_n_396_, 2);
v___x_399_ = lean_box(0);
v___x_400_ = lean_array_get_borrowed(v___x_399_, v_args_398_, v_i_397_);
lean_inc(v___x_400_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_401_, lean_object* v_i_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_SyntaxNode_getArg(v_n_401_, v_i_402_);
lean_dec(v_i_402_);
lean_dec(v_n_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_404_){
_start:
{
lean_object* v_args_405_; 
v_args_405_ = lean_ctor_get(v_n_404_, 2);
lean_inc_ref(v_args_405_);
return v_args_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_SyntaxNode_getArgs(v_n_406_);
lean_dec(v_n_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_408_, lean_object* v_fn_409_){
_start:
{
lean_object* v_info_410_; lean_object* v_kind_411_; lean_object* v_args_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_info_410_ = lean_ctor_get(v_n_408_, 0);
v_kind_411_ = lean_ctor_get(v_n_408_, 1);
v_args_412_ = lean_ctor_get(v_n_408_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_n_408_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v_n_408_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_args_412_);
lean_inc(v_kind_411_);
lean_inc(v_info_410_);
lean_dec(v_n_408_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_apply_1(v_fn_409_, v_args_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_info_410_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_kind_411_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_421_, lean_object* v_x_422_){
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
lean_object* v_val_426_; lean_object* v_val_427_; uint8_t v___x_428_; 
v_val_426_ = lean_ctor_get(v_x_421_, 0);
v_val_427_ = lean_ctor_get(v_x_422_, 0);
v___x_428_ = l_Lean_Syntax_instBEqRange_beq(v_val_426_, v_val_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_421_ = stack[0].m_obj;
lean_object* v_x_422_ = stack[1].m_obj;
uint8_t v_res_429_;
v_res_429_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_421_, v_x_422_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec(v_x_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_434_, lean_object* v_x_435_){
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
LEAN_EXPORT void l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_434_ = stack[0].m_obj;
lean_object* v_x_435_ = stack[1].m_obj;
uint8_t v_res_445_;
v_res_445_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_434_, v_x_435_);
stack->m_num = v_res_445_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_446_, v_x_447_);
lean_dec(v_x_447_);
lean_dec(v_x_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
switch(lean_obj_tag(v_x_450_))
{
case 0:
{
if (lean_obj_tag(v_x_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 1;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
lean_dec(v_x_451_);
v___x_453_ = 0;
return v___x_453_;
}
}
case 1:
{
if (lean_obj_tag(v_x_451_) == 1)
{
lean_object* v_info_454_; lean_object* v_kind_455_; lean_object* v_args_456_; lean_object* v_info_457_; lean_object* v_kind_458_; lean_object* v_args_459_; uint8_t v___y_461_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_info_454_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_info_454_);
v_kind_455_ = lean_ctor_get(v_x_450_, 1);
lean_inc(v_kind_455_);
v_args_456_ = lean_ctor_get(v_x_450_, 2);
lean_inc_ref(v_args_456_);
lean_dec_ref_known(v_x_450_, 3);
v_info_457_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_info_457_);
v_kind_458_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_kind_458_);
v_args_459_ = lean_ctor_get(v_x_451_, 2);
lean_inc_ref(v_args_459_);
lean_dec_ref_known(v_x_451_, 3);
v___x_466_ = 0;
v___x_467_ = l_Lean_SourceInfo_getRange_x3f(v___x_466_, v_info_454_);
lean_dec(v_info_454_);
v___x_468_ = l_Lean_SourceInfo_getRange_x3f(v___x_466_, v_info_457_);
lean_dec(v_info_457_);
v___x_469_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_467_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_467_);
if (v___x_469_ == 0)
{
lean_dec(v_kind_458_);
lean_dec(v_kind_455_);
v___y_461_ = v___x_469_;
goto v___jp_460_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = lean_name_eq(v_kind_455_, v_kind_458_);
lean_dec(v_kind_458_);
lean_dec(v_kind_455_);
v___y_461_ = v___x_470_;
goto v___jp_460_;
}
v___jp_460_:
{
if (v___y_461_ == 0)
{
lean_dec_ref(v_args_459_);
lean_dec_ref(v_args_456_);
return v___y_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_array_get_size(v_args_456_);
v___x_463_ = lean_array_get_size(v_args_459_);
v___x_464_ = lean_nat_dec_eq(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec_ref(v_args_459_);
lean_dec_ref(v_args_456_);
return v___x_464_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_args_456_, v_args_459_, v___x_462_);
lean_dec_ref(v_args_459_);
lean_dec_ref(v_args_456_);
return v___x_465_;
}
}
}
}
else
{
uint8_t v___x_471_; 
lean_dec_ref_known(v_x_450_, 3);
lean_dec(v_x_451_);
v___x_471_ = 0;
return v___x_471_;
}
}
case 2:
{
if (lean_obj_tag(v_x_451_) == 2)
{
lean_object* v_info_472_; lean_object* v_val_473_; lean_object* v_info_474_; lean_object* v_val_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_info_472_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_info_472_);
v_val_473_ = lean_ctor_get(v_x_450_, 1);
lean_inc_ref(v_val_473_);
lean_dec_ref_known(v_x_450_, 2);
v_info_474_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_info_474_);
v_val_475_ = lean_ctor_get(v_x_451_, 1);
lean_inc_ref(v_val_475_);
lean_dec_ref_known(v_x_451_, 2);
v___x_476_ = 0;
v___x_477_ = l_Lean_SourceInfo_getRange_x3f(v___x_476_, v_info_472_);
lean_dec(v_info_472_);
v___x_478_ = l_Lean_SourceInfo_getRange_x3f(v___x_476_, v_info_474_);
lean_dec(v_info_474_);
v___x_479_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_477_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_477_);
if (v___x_479_ == 0)
{
lean_dec_ref(v_val_475_);
lean_dec_ref(v_val_473_);
return v___x_479_;
}
else
{
uint8_t v___x_480_; 
v___x_480_ = lean_string_dec_eq(v_val_473_, v_val_475_);
lean_dec_ref(v_val_475_);
lean_dec_ref(v_val_473_);
return v___x_480_;
}
}
else
{
uint8_t v___x_481_; 
lean_dec_ref_known(v_x_450_, 2);
lean_dec(v_x_451_);
v___x_481_ = 0;
return v___x_481_;
}
}
default: 
{
if (lean_obj_tag(v_x_451_) == 3)
{
lean_object* v_info_482_; lean_object* v_rawVal_483_; lean_object* v_val_484_; lean_object* v_preresolved_485_; lean_object* v_info_486_; lean_object* v_rawVal_487_; lean_object* v_val_488_; lean_object* v_preresolved_489_; uint8_t v___y_491_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_info_482_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_info_482_);
v_rawVal_483_ = lean_ctor_get(v_x_450_, 1);
lean_inc_ref(v_rawVal_483_);
v_val_484_ = lean_ctor_get(v_x_450_, 2);
lean_inc(v_val_484_);
v_preresolved_485_ = lean_ctor_get(v_x_450_, 3);
lean_inc(v_preresolved_485_);
lean_dec_ref_known(v_x_450_, 4);
v_info_486_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_info_486_);
v_rawVal_487_ = lean_ctor_get(v_x_451_, 1);
lean_inc_ref(v_rawVal_487_);
v_val_488_ = lean_ctor_get(v_x_451_, 2);
lean_inc(v_val_488_);
v_preresolved_489_ = lean_ctor_get(v_x_451_, 3);
lean_inc(v_preresolved_489_);
lean_dec_ref_known(v_x_451_, 4);
v___x_494_ = 0;
v___x_495_ = l_Lean_SourceInfo_getRange_x3f(v___x_494_, v_info_482_);
lean_dec(v_info_482_);
v___x_496_ = l_Lean_SourceInfo_getRange_x3f(v___x_494_, v_info_486_);
lean_dec(v_info_486_);
v___x_497_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_495_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v___x_495_);
if (v___x_497_ == 0)
{
lean_dec_ref(v_rawVal_487_);
lean_dec_ref(v_rawVal_483_);
v___y_491_ = v___x_497_;
goto v___jp_490_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = l_Substring_Raw_beq(v_rawVal_483_, v_rawVal_487_);
v___y_491_ = v___x_498_;
goto v___jp_490_;
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_dec(v_preresolved_489_);
lean_dec(v_val_488_);
lean_dec(v_preresolved_485_);
lean_dec(v_val_484_);
return v___y_491_;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = lean_name_eq(v_val_484_, v_val_488_);
lean_dec(v_val_488_);
lean_dec(v_val_484_);
if (v___x_492_ == 0)
{
lean_dec(v_preresolved_489_);
lean_dec(v_preresolved_485_);
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_485_, v_preresolved_489_);
lean_dec(v_preresolved_489_);
lean_dec(v_preresolved_485_);
return v___x_493_;
}
}
}
}
else
{
uint8_t v___x_499_; 
lean_dec_ref_known(v_x_450_, 4);
lean_dec(v_x_451_);
v___x_499_ = 0;
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_structRangeEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_450_ = stack[0].m_obj;
lean_object* v_x_451_ = stack[1].m_obj;
uint8_t v_res_500_;
v_res_500_ = l_Lean_Syntax_structRangeEq(v_x_450_, v_x_451_);
stack->m_num = v_res_500_;
}
uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object* v_xs_501_, lean_object* v_ys_502_, lean_object* v_x_503_){
_start:
{
lean_object* v_zero_504_; uint8_t v_isZero_505_; 
v_zero_504_ = lean_unsigned_to_nat(0u);
v_isZero_505_ = lean_nat_dec_eq(v_x_503_, v_zero_504_);
if (v_isZero_505_ == 1)
{
lean_dec(v_x_503_);
return v_isZero_505_;
}
else
{
lean_object* v_one_506_; lean_object* v_n_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_one_506_ = lean_unsigned_to_nat(1u);
v_n_507_ = lean_nat_sub(v_x_503_, v_one_506_);
lean_dec(v_x_503_);
v___x_508_ = lean_array_fget_borrowed(v_xs_501_, v_n_507_);
v___x_509_ = lean_array_fget_borrowed(v_ys_502_, v_n_507_);
lean_inc(v___x_509_);
lean_inc(v___x_508_);
v___x_510_ = l_Lean_Syntax_structRangeEq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec(v_n_507_);
return v___x_510_;
}
else
{
v_x_503_ = v_n_507_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_501_ = stack[0].m_obj;
lean_object* v_ys_502_ = stack[1].m_obj;
lean_object* v_x_503_ = stack[2].m_obj;
uint8_t v_res_512_;
v_res_512_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_501_, v_ys_502_, v_x_503_);
stack->m_num = v_res_512_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object* v_xs_513_, lean_object* v_ys_514_, lean_object* v_x_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_513_, v_ys_514_, v_x_515_);
lean_dec_ref(v_ys_514_);
lean_dec_ref(v_xs_513_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Lean_Syntax_structRangeEq(v_x_518_, v_x_519_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_xs_522_, lean_object* v_ys_523_, lean_object* v_hsz_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_522_, v_ys_523_, v_x_525_);
return v___x_527_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_522_ = stack[0].m_obj;
lean_object* v_ys_523_ = stack[1].m_obj;
lean_object* v_x_525_ = stack[3].m_obj;
uint8_t v_res_528_;
v_res_528_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_522_, v_ys_523_, lean_box(0), v_x_525_, lean_box(0));
stack->m_num = v_res_528_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_xs_529_, lean_object* v_ys_530_, lean_object* v_hsz_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_529_, v_ys_530_, v_hsz_531_, v_x_532_, v_x_533_);
lean_dec_ref(v_ys_530_);
lean_dec_ref(v_xs_529_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_536_, lean_object* v_x_537_){
_start:
{
return v___x_536_;
}
}
LEAN_EXPORT void l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_536_ = stack[0].m_num;
lean_object* v_x_537_ = stack[1].m_obj;
uint8_t v_res_538_;
v_res_538_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_536_, v_x_537_);
stack->m_num = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_539_, lean_object* v_x_540_){
_start:
{
uint8_t v___x_92__boxed_541_; uint8_t v_res_542_; lean_object* v_r_543_; 
v___x_92__boxed_541_ = lean_unbox(v___x_539_);
v_res_542_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_92__boxed_541_, v_x_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_553_, lean_object* v_stx1_554_, lean_object* v_stx2_555_){
_start:
{
uint8_t v___x_556_; uint8_t v___x_557_; 
lean_inc(v_stx2_555_);
lean_inc(v_stx1_554_);
v___x_556_ = l_Lean_Syntax_structRangeEq(v_stx1_554_, v_stx2_555_);
v___x_557_ = 1;
if (v___x_556_ == 0)
{
lean_object* v_map_558_; lean_object* v___x_559_; lean_object* v___f_560_; uint8_t v___y_562_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_map_558_ = lean_ctor_get(v_opts_553_, 0);
v___x_559_ = lean_box(v___x_556_);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_560_, 0, v___x_559_);
v___x_577_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_558_, v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
v___y_562_ = v___x_556_;
goto v___jp_561_;
}
else
{
lean_object* v_val_579_; 
v_val_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_578_, 1);
if (lean_obj_tag(v_val_579_) == 1)
{
uint8_t v_v_580_; 
v_v_580_ = lean_ctor_get_uint8(v_val_579_, 0);
lean_dec_ref_known(v_val_579_, 0);
v___y_562_ = v_v_580_;
goto v___jp_561_;
}
else
{
lean_dec(v_val_579_);
v___y_562_ = v___x_556_;
goto v___jp_561_;
}
}
v___jp_561_:
{
if (v___y_562_ == 0)
{
lean_dec_ref(v___f_560_);
lean_dec(v_stx2_555_);
lean_dec(v_stx1_554_);
return v___x_556_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_563_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_564_ = lean_box(0);
v___x_565_ = l_Lean_Syntax_formatStx(v_stx1_554_, v___x_564_, v___x_557_);
v___x_566_ = l_Std_Format_defWidth;
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Std_Format_pretty(v___x_565_, v___x_566_, v___x_567_, v___x_567_);
v___x_569_ = lean_string_append(v___x_563_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
v___x_572_ = l_Lean_Syntax_formatStx(v_stx2_555_, v___x_564_, v___x_557_);
v___x_573_ = l_Std_Format_pretty(v___x_572_, v___x_566_, v___x_567_, v___x_567_);
v___x_574_ = lean_string_append(v___x_571_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = lean_dbg_trace(v___x_574_, v___f_560_);
v___x_576_ = lean_unbox(v___x_575_);
lean_dec(v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_dec(v_stx2_555_);
lean_dec(v_stx1_554_);
return v___x_557_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_structRangeEqWithTraceReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_553_ = stack[0].m_obj;
lean_object* v_stx1_554_ = stack[1].m_obj;
lean_object* v_stx2_555_ = stack[2].m_obj;
uint8_t v_res_581_;
v_res_581_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_553_, v_stx1_554_, v_stx2_555_);
stack->m_num = v_res_581_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_582_, lean_object* v_stx1_583_, lean_object* v_stx2_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_582_, v_stx1_583_, v_stx2_584_);
lean_dec_ref(v_opts_582_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
switch(lean_obj_tag(v_x_587_))
{
case 0:
{
if (lean_obj_tag(v_x_588_) == 0)
{
uint8_t v___x_589_; 
v___x_589_ = 1;
return v___x_589_;
}
else
{
uint8_t v___x_590_; 
lean_dec(v_x_588_);
v___x_590_ = 0;
return v___x_590_;
}
}
case 1:
{
if (lean_obj_tag(v_x_588_) == 1)
{
lean_object* v_info_591_; lean_object* v_kind_592_; lean_object* v_args_593_; lean_object* v_info_594_; lean_object* v_kind_595_; lean_object* v_args_596_; uint8_t v___y_598_; uint8_t v___x_603_; 
v_info_591_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_info_591_);
v_kind_592_ = lean_ctor_get(v_x_587_, 1);
lean_inc(v_kind_592_);
v_args_593_ = lean_ctor_get(v_x_587_, 2);
lean_inc_ref(v_args_593_);
lean_dec_ref_known(v_x_587_, 3);
v_info_594_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_info_594_);
v_kind_595_ = lean_ctor_get(v_x_588_, 1);
lean_inc(v_kind_595_);
v_args_596_ = lean_ctor_get(v_x_588_, 2);
lean_inc_ref(v_args_596_);
lean_dec_ref_known(v_x_588_, 3);
v___x_603_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_591_, v_info_594_);
if (v___x_603_ == 0)
{
lean_dec(v_kind_595_);
lean_dec(v_kind_592_);
v___y_598_ = v___x_603_;
goto v___jp_597_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = lean_name_eq(v_kind_592_, v_kind_595_);
lean_dec(v_kind_595_);
lean_dec(v_kind_592_);
v___y_598_ = v___x_604_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_dec_ref(v_args_596_);
lean_dec_ref(v_args_593_);
return v___y_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = lean_array_get_size(v_args_593_);
v___x_600_ = lean_array_get_size(v_args_596_);
v___x_601_ = lean_nat_dec_eq(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec_ref(v_args_596_);
lean_dec_ref(v_args_593_);
return v___x_601_;
}
else
{
uint8_t v___x_602_; 
v___x_602_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_593_, v_args_596_, v___x_599_);
lean_dec_ref(v_args_596_);
lean_dec_ref(v_args_593_);
return v___x_602_;
}
}
}
}
else
{
uint8_t v___x_605_; 
lean_dec_ref_known(v_x_587_, 3);
lean_dec(v_x_588_);
v___x_605_ = 0;
return v___x_605_;
}
}
case 2:
{
if (lean_obj_tag(v_x_588_) == 2)
{
lean_object* v_info_606_; lean_object* v_val_607_; lean_object* v_info_608_; lean_object* v_val_609_; uint8_t v___x_610_; 
v_info_606_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_info_606_);
v_val_607_ = lean_ctor_get(v_x_587_, 1);
lean_inc_ref(v_val_607_);
lean_dec_ref_known(v_x_587_, 2);
v_info_608_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_info_608_);
v_val_609_ = lean_ctor_get(v_x_588_, 1);
lean_inc_ref(v_val_609_);
lean_dec_ref_known(v_x_588_, 2);
v___x_610_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_606_, v_info_608_);
if (v___x_610_ == 0)
{
lean_dec_ref(v_val_609_);
lean_dec_ref(v_val_607_);
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_string_dec_eq(v_val_607_, v_val_609_);
lean_dec_ref(v_val_609_);
lean_dec_ref(v_val_607_);
return v___x_611_;
}
}
else
{
uint8_t v___x_612_; 
lean_dec_ref_known(v_x_587_, 2);
lean_dec(v_x_588_);
v___x_612_ = 0;
return v___x_612_;
}
}
default: 
{
if (lean_obj_tag(v_x_588_) == 3)
{
lean_object* v_info_613_; lean_object* v_rawVal_614_; lean_object* v_val_615_; lean_object* v_preresolved_616_; lean_object* v_info_617_; lean_object* v_rawVal_618_; lean_object* v_val_619_; lean_object* v_preresolved_620_; uint8_t v___y_622_; uint8_t v___x_625_; 
v_info_613_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_info_613_);
v_rawVal_614_ = lean_ctor_get(v_x_587_, 1);
lean_inc_ref(v_rawVal_614_);
v_val_615_ = lean_ctor_get(v_x_587_, 2);
lean_inc(v_val_615_);
v_preresolved_616_ = lean_ctor_get(v_x_587_, 3);
lean_inc(v_preresolved_616_);
lean_dec_ref_known(v_x_587_, 4);
v_info_617_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_info_617_);
v_rawVal_618_ = lean_ctor_get(v_x_588_, 1);
lean_inc_ref(v_rawVal_618_);
v_val_619_ = lean_ctor_get(v_x_588_, 2);
lean_inc(v_val_619_);
v_preresolved_620_ = lean_ctor_get(v_x_588_, 3);
lean_inc(v_preresolved_620_);
lean_dec_ref_known(v_x_588_, 4);
v___x_625_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_613_, v_info_617_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_rawVal_618_);
lean_dec_ref(v_rawVal_614_);
v___y_622_ = v___x_625_;
goto v___jp_621_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = l_Substring_Raw_beq(v_rawVal_614_, v_rawVal_618_);
v___y_622_ = v___x_626_;
goto v___jp_621_;
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_dec(v_preresolved_620_);
lean_dec(v_val_619_);
lean_dec(v_preresolved_616_);
lean_dec(v_val_615_);
return v___y_622_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = lean_name_eq(v_val_615_, v_val_619_);
lean_dec(v_val_619_);
lean_dec(v_val_615_);
if (v___x_623_ == 0)
{
lean_dec(v_preresolved_620_);
lean_dec(v_preresolved_616_);
return v___x_623_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_616_, v_preresolved_620_);
lean_dec(v_preresolved_620_);
lean_dec(v_preresolved_616_);
return v___x_624_;
}
}
}
}
else
{
uint8_t v___x_627_; 
lean_dec_ref_known(v_x_587_, 4);
lean_dec(v_x_588_);
v___x_627_ = 0;
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_eqWithInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_587_ = stack[0].m_obj;
lean_object* v_x_588_ = stack[1].m_obj;
uint8_t v_res_628_;
v_res_628_ = l_Lean_Syntax_eqWithInfo(v_x_587_, v_x_588_);
stack->m_num = v_res_628_;
}
uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_629_, lean_object* v_ys_630_, lean_object* v_x_631_){
_start:
{
lean_object* v_zero_632_; uint8_t v_isZero_633_; 
v_zero_632_ = lean_unsigned_to_nat(0u);
v_isZero_633_ = lean_nat_dec_eq(v_x_631_, v_zero_632_);
if (v_isZero_633_ == 1)
{
lean_dec(v_x_631_);
return v_isZero_633_;
}
else
{
lean_object* v_one_634_; lean_object* v_n_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_one_634_ = lean_unsigned_to_nat(1u);
v_n_635_ = lean_nat_sub(v_x_631_, v_one_634_);
lean_dec(v_x_631_);
v___x_636_ = lean_array_fget_borrowed(v_xs_629_, v_n_635_);
v___x_637_ = lean_array_fget_borrowed(v_ys_630_, v_n_635_);
lean_inc(v___x_637_);
lean_inc(v___x_636_);
v___x_638_ = l_Lean_Syntax_eqWithInfo(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v_n_635_);
return v___x_638_;
}
else
{
v_x_631_ = v_n_635_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_629_ = stack[0].m_obj;
lean_object* v_ys_630_ = stack[1].m_obj;
lean_object* v_x_631_ = stack[2].m_obj;
uint8_t v_res_640_;
v_res_640_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_629_, v_ys_630_, v_x_631_);
stack->m_num = v_res_640_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_641_, lean_object* v_ys_642_, lean_object* v_x_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_641_, v_ys_642_, v_x_643_);
lean_dec_ref(v_ys_642_);
lean_dec_ref(v_xs_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lean_Syntax_eqWithInfo(v_x_646_, v_x_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_650_, lean_object* v_ys_651_, lean_object* v_hsz_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_650_, v_ys_651_, v_x_653_);
return v___x_655_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_650_ = stack[0].m_obj;
lean_object* v_ys_651_ = stack[1].m_obj;
lean_object* v_x_653_ = stack[3].m_obj;
uint8_t v_res_656_;
v_res_656_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_650_, v_ys_651_, lean_box(0), v_x_653_, lean_box(0));
stack->m_num = v_res_656_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_657_, lean_object* v_ys_658_, lean_object* v_hsz_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_657_, v_ys_658_, v_hsz_659_, v_x_660_, v_x_661_);
lean_dec_ref(v_ys_658_);
lean_dec_ref(v_xs_657_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_664_, lean_object* v_stx1_665_, lean_object* v_stx2_666_){
_start:
{
uint8_t v___x_667_; uint8_t v___x_668_; 
lean_inc(v_stx2_666_);
lean_inc(v_stx1_665_);
v___x_667_ = l_Lean_Syntax_eqWithInfo(v_stx1_665_, v_stx2_666_);
v___x_668_ = 1;
if (v___x_667_ == 0)
{
lean_object* v_map_669_; lean_object* v___x_670_; lean_object* v___f_671_; uint8_t v___y_673_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_map_669_ = lean_ctor_get(v_opts_664_, 0);
v___x_670_ = lean_box(v___x_667_);
v___f_671_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_671_, 0, v___x_670_);
v___x_688_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_689_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_669_, v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
v___y_673_ = v___x_667_;
goto v___jp_672_;
}
else
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_689_, 1);
if (lean_obj_tag(v_val_690_) == 1)
{
uint8_t v_v_691_; 
v_v_691_ = lean_ctor_get_uint8(v_val_690_, 0);
lean_dec_ref_known(v_val_690_, 0);
v___y_673_ = v_v_691_;
goto v___jp_672_;
}
else
{
lean_dec(v_val_690_);
v___y_673_ = v___x_667_;
goto v___jp_672_;
}
}
v___jp_672_:
{
if (v___y_673_ == 0)
{
lean_dec_ref(v___f_671_);
lean_dec(v_stx2_666_);
lean_dec(v_stx1_665_);
return v___x_667_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_674_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_Syntax_formatStx(v_stx1_665_, v___x_675_, v___x_668_);
v___x_677_ = l_Std_Format_defWidth;
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = l_Std_Format_pretty(v___x_676_, v___x_677_, v___x_678_, v___x_678_);
v___x_680_ = lean_string_append(v___x_674_, v___x_679_);
lean_dec_ref(v___x_679_);
v___x_681_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
v___x_683_ = l_Lean_Syntax_formatStx(v_stx2_666_, v___x_675_, v___x_668_);
v___x_684_ = l_Std_Format_pretty(v___x_683_, v___x_677_, v___x_678_, v___x_678_);
v___x_685_ = lean_string_append(v___x_682_, v___x_684_);
lean_dec_ref(v___x_684_);
v___x_686_ = lean_dbg_trace(v___x_685_, v___f_671_);
v___x_687_ = lean_unbox(v___x_686_);
lean_dec(v___x_686_);
return v___x_687_;
}
}
}
else
{
lean_dec(v_stx2_666_);
lean_dec(v_stx1_665_);
return v___x_668_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_eqWithInfoAndTraceReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_664_ = stack[0].m_obj;
lean_object* v_stx1_665_ = stack[1].m_obj;
lean_object* v_stx2_666_ = stack[2].m_obj;
uint8_t v_res_692_;
v_res_692_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_664_, v_stx1_665_, v_stx2_666_);
stack->m_num = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_693_, lean_object* v_stx1_694_, lean_object* v_stx2_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_693_, v_stx1_694_, v_stx2_695_);
lean_dec_ref(v_opts_693_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 2)
{
lean_object* v_val_700_; 
v_val_700_ = lean_ctor_get(v_x_699_, 1);
lean_inc_ref(v_val_700_);
return v_val_700_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Syntax_getAtomVal(v_x_702_);
lean_dec(v_x_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_704_) == 2)
{
lean_object* v_info_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_info_706_ = lean_ctor_get(v_x_704_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_x_704_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v_x_704_, 1);
lean_dec(v_unused_714_);
v___x_708_ = v_x_704_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_info_706_);
lean_dec(v_x_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_x_705_);
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_info_706_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_x_705_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_dec_ref(v_x_705_);
return v_x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_715_, lean_object* v_hyes_716_, lean_object* v_hno_717_){
_start:
{
if (lean_obj_tag(v_stx_715_) == 1)
{
lean_object* v___x_718_; 
lean_dec(v_hno_717_);
v___x_718_ = lean_apply_1(v_hyes_716_, v_stx_715_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v_hyes_716_);
lean_dec(v_stx_715_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_apply_1(v_hno_717_, v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_721_, lean_object* v_stx_722_, lean_object* v_hyes_723_, lean_object* v_hno_724_){
_start:
{
if (lean_obj_tag(v_stx_722_) == 1)
{
lean_object* v___x_725_; 
lean_dec(v_hno_724_);
v___x_725_ = lean_apply_1(v_hyes_723_, v_stx_722_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v_hyes_723_);
lean_dec(v_stx_722_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_apply_1(v_hno_724_, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_728_, lean_object* v_kind_729_, lean_object* v_hyes_730_, lean_object* v_hno_731_){
_start:
{
if (lean_obj_tag(v_stx_728_) == 1)
{
lean_object* v_kind_732_; uint8_t v___x_733_; 
v_kind_732_ = lean_ctor_get(v_stx_728_, 1);
v___x_733_ = lean_name_eq(v_kind_732_, v_kind_729_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref_known(v_stx_728_, 3);
lean_dec(v_hyes_730_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_apply_1(v_hno_731_, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; 
lean_dec(v_hno_731_);
v___x_736_ = lean_apply_1(v_hyes_730_, v_stx_728_);
return v___x_736_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec(v_hyes_730_);
lean_dec(v_stx_728_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_apply_1(v_hno_731_, v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_739_, lean_object* v_kind_740_, lean_object* v_hyes_741_, lean_object* v_hno_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_739_, v_kind_740_, v_hyes_741_, v_hno_742_);
lean_dec(v_kind_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_744_, lean_object* v_stx_745_, lean_object* v_kind_746_, lean_object* v_hyes_747_, lean_object* v_hno_748_){
_start:
{
if (lean_obj_tag(v_stx_745_) == 1)
{
lean_object* v_kind_749_; uint8_t v___x_750_; 
v_kind_749_ = lean_ctor_get(v_stx_745_, 1);
v___x_750_ = lean_name_eq(v_kind_749_, v_kind_746_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref_known(v_stx_745_, 3);
lean_dec(v_hyes_747_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_apply_1(v_hno_748_, v___x_751_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
lean_dec(v_hno_748_);
v___x_753_ = lean_apply_1(v_hyes_747_, v_stx_745_);
return v___x_753_;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_hyes_747_);
lean_dec(v_stx_745_);
v___x_754_ = lean_box(0);
v___x_755_ = lean_apply_1(v_hno_748_, v___x_754_);
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_756_, lean_object* v_stx_757_, lean_object* v_kind_758_, lean_object* v_hyes_759_, lean_object* v_hno_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_756_, v_stx_757_, v_kind_758_, v_hyes_759_, v_hno_760_);
lean_dec(v_kind_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 1)
{
lean_inc_ref(v_x_771_);
return v_x_771_;
}
else
{
lean_object* v___x_772_; 
v___x_772_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Syntax_asNode(v_x_773_);
lean_dec(v_x_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_775_, lean_object* v_i_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = l_Lean_Syntax_getArg(v_stx_775_, v_i_776_);
v___x_778_ = l_Lean_Syntax_getId(v___x_777_);
lean_dec(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_779_, lean_object* v_i_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Syntax_getIdAt(v_stx_779_, v_i_780_);
lean_dec(v_i_780_);
lean_dec(v_stx_779_);
return v_res_781_;
}
}
uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_782_, lean_object* v_x_783_){
_start:
{
switch(lean_obj_tag(v_x_783_))
{
case 3:
{
lean_object* v_val_784_; uint8_t v___x_785_; 
v_val_784_ = lean_ctor_get(v_x_783_, 2);
v___x_785_ = lean_name_eq(v_id_782_, v_val_784_);
return v___x_785_;
}
case 1:
{
lean_object* v_args_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_args_786_ = lean_ctor_get(v_x_783_, 2);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_array_get_size(v_args_786_);
v___x_789_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
return v___x_789_;
}
else
{
if (v___x_789_ == 0)
{
return v___x_789_;
}
else
{
size_t v___x_790_; size_t v___x_791_; uint8_t v___x_792_; 
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_788_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_782_, v_args_786_, v___x_790_, v___x_791_);
return v___x_792_;
}
}
}
default: 
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_hasIdent_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_782_ = stack[0].m_obj;
lean_object* v_x_783_ = stack[1].m_obj;
uint8_t v_res_794_;
v_res_794_ = l_Lean_Syntax_hasIdent(v_id_782_, v_x_783_);
stack->m_num = v_res_794_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_795_, lean_object* v_as_796_, size_t v_i_797_, size_t v_stop_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_797_, v_stop_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_array_uget_borrowed(v_as_796_, v_i_797_);
v___x_801_ = l_Lean_Syntax_hasIdent(v_id_795_, v___x_800_);
if (v___x_801_ == 0)
{
size_t v___x_802_; size_t v___x_803_; 
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_797_, v___x_802_);
v_i_797_ = v___x_803_;
goto _start;
}
else
{
return v___x_801_;
}
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_795_ = stack[0].m_obj;
lean_object* v_as_796_ = stack[1].m_obj;
size_t v_i_797_ = stack[2].m_num;
size_t v_stop_798_ = stack[3].m_num;
uint8_t v_res_806_;
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_795_, v_as_796_, v_i_797_, v_stop_798_);
stack->m_num = v_res_806_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_807_, lean_object* v_as_808_, lean_object* v_i_809_, lean_object* v_stop_810_){
_start:
{
size_t v_i_boxed_811_; size_t v_stop_boxed_812_; uint8_t v_res_813_; lean_object* v_r_814_; 
v_i_boxed_811_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_stop_boxed_812_ = lean_unbox_usize(v_stop_810_);
lean_dec(v_stop_810_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_807_, v_as_808_, v_i_boxed_811_, v_stop_boxed_812_);
lean_dec_ref(v_as_808_);
lean_dec(v_id_807_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_815_, lean_object* v_x_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Lean_Syntax_hasIdent(v_id_815_, v_x_816_);
lean_dec(v_x_816_);
lean_dec(v_id_815_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_819_, lean_object* v_fn_820_){
_start:
{
if (lean_obj_tag(v_stx_819_) == 1)
{
lean_object* v_info_821_; lean_object* v_kind_822_; lean_object* v_args_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_info_821_ = lean_ctor_get(v_stx_819_, 0);
v_kind_822_ = lean_ctor_get(v_stx_819_, 1);
v_args_823_ = lean_ctor_get(v_stx_819_, 2);
v_isSharedCheck_831_ = !lean_is_exclusive(v_stx_819_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v_stx_819_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_args_823_);
lean_inc(v_kind_822_);
lean_inc(v_info_821_);
lean_dec(v_stx_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_apply_1(v_fn_820_, v_args_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 2, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_info_821_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_kind_822_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_dec_ref(v_fn_820_);
return v_stx_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_832_, lean_object* v_i_833_, lean_object* v_fn_834_){
_start:
{
if (lean_obj_tag(v_stx_832_) == 1)
{
lean_object* v_info_835_; lean_object* v_kind_836_; lean_object* v_args_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_info_835_ = lean_ctor_get(v_stx_832_, 0);
v_kind_836_ = lean_ctor_get(v_stx_832_, 1);
v_args_837_ = lean_ctor_get(v_stx_832_, 2);
v___x_838_ = lean_array_get_size(v_args_837_);
v___x_839_ = lean_nat_dec_lt(v_i_833_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v_fn_834_);
return v_stx_832_;
}
else
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_851_; 
lean_inc_ref(v_args_837_);
lean_inc(v_kind_836_);
lean_inc(v_info_835_);
v_isSharedCheck_851_ = !lean_is_exclusive(v_stx_832_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; lean_object* v_unused_854_; 
v_unused_852_ = lean_ctor_get(v_stx_832_, 2);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_stx_832_, 1);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_stx_832_, 0);
lean_dec(v_unused_854_);
v___x_841_ = v_stx_832_;
v_isShared_842_ = v_isSharedCheck_851_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_stx_832_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_851_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_v_843_; lean_object* v___x_844_; lean_object* v_xs_x27_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v_v_843_ = lean_array_fget(v_args_837_, v_i_833_);
v___x_844_ = lean_box(0);
v_xs_x27_845_ = lean_array_fset(v_args_837_, v_i_833_, v___x_844_);
v___x_846_ = lean_apply_1(v_fn_834_, v_v_843_);
v___x_847_ = lean_array_fset(v_xs_x27_845_, v_i_833_, v___x_846_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 2, v___x_847_);
v___x_849_ = v___x_841_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_info_835_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_kind_836_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_dec_ref(v_fn_834_);
return v_stx_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_855_, lean_object* v_i_856_, lean_object* v_fn_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Syntax_modifyArg(v_stx_855_, v_i_856_, v_fn_857_);
lean_dec(v_i_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_859_, lean_object* v_kind_860_, lean_object* v_toPure_861_, lean_object* v_____do__lift_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v_info_859_);
lean_ctor_set(v___x_863_, 1, v_kind_860_);
lean_ctor_set(v___x_863_, 2, v_____do__lift_862_);
v___x_864_ = lean_apply_2(v_toPure_861_, lean_box(0), v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_865_, lean_object* v_x_866_, lean_object* v_o_867_){
_start:
{
if (lean_obj_tag(v_o_867_) == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_apply_2(v_toPure_865_, lean_box(0), v_x_866_);
return v___x_868_;
}
else
{
lean_object* v_val_869_; lean_object* v___x_870_; 
lean_dec(v_x_866_);
v_val_869_ = lean_ctor_get(v_o_867_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_o_867_, 1);
v___x_870_ = lean_apply_2(v_toPure_865_, lean_box(0), v_val_869_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_871_, lean_object* v_fn_872_, lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_873_) == 1)
{
lean_object* v_toApplicative_874_; lean_object* v_toBind_875_; lean_object* v_toPure_876_; lean_object* v_info_877_; lean_object* v_kind_878_; lean_object* v_args_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_toApplicative_874_ = lean_ctor_get(v_inst_871_, 0);
v_toBind_875_ = lean_ctor_get(v_inst_871_, 1);
lean_inc_n(v_toBind_875_, 2);
v_toPure_876_ = lean_ctor_get(v_toApplicative_874_, 1);
lean_inc_n(v_toPure_876_, 2);
v_info_877_ = lean_ctor_get(v_x_873_, 0);
v_kind_878_ = lean_ctor_get(v_x_873_, 1);
v_args_879_ = lean_ctor_get(v_x_873_, 2);
lean_inc(v_kind_878_);
lean_inc(v_info_877_);
v___f_880_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_880_, 0, v_info_877_);
lean_closure_set(v___f_880_, 1, v_kind_878_);
lean_closure_set(v___f_880_, 2, v_toPure_876_);
lean_inc_ref(v_args_879_);
lean_inc(v_fn_872_);
v___f_881_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_881_, 0, v_inst_871_);
lean_closure_set(v___f_881_, 1, v_fn_872_);
lean_closure_set(v___f_881_, 2, v_args_879_);
lean_closure_set(v___f_881_, 3, v_toBind_875_);
lean_closure_set(v___f_881_, 4, v___f_880_);
lean_closure_set(v___f_881_, 5, v_toPure_876_);
v___x_882_ = lean_apply_1(v_fn_872_, v_x_873_);
v___x_883_ = lean_apply_4(v_toBind_875_, lean_box(0), lean_box(0), v___x_882_, v___f_881_);
return v___x_883_;
}
else
{
lean_object* v_toApplicative_884_; lean_object* v_toBind_885_; lean_object* v_toPure_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_toApplicative_884_ = lean_ctor_get(v_inst_871_, 0);
lean_inc_ref(v_toApplicative_884_);
v_toBind_885_ = lean_ctor_get(v_inst_871_, 1);
lean_inc(v_toBind_885_);
lean_dec_ref(v_inst_871_);
v_toPure_886_ = lean_ctor_get(v_toApplicative_884_, 1);
lean_inc(v_toPure_886_);
lean_dec_ref(v_toApplicative_884_);
lean_inc(v_x_873_);
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_887_, 0, v_toPure_886_);
lean_closure_set(v___f_887_, 1, v_x_873_);
v___x_888_ = lean_apply_1(v_fn_872_, v_x_873_);
v___x_889_ = lean_apply_4(v_toBind_885_, lean_box(0), lean_box(0), v___x_888_, v___f_887_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_890_, lean_object* v_fn_891_, lean_object* v_args_892_, lean_object* v_toBind_893_, lean_object* v___f_894_, lean_object* v_toPure_895_, lean_object* v_____do__lift_896_){
_start:
{
if (lean_obj_tag(v_____do__lift_896_) == 0)
{
lean_object* v___x_897_; size_t v_sz_898_; size_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_toPure_895_);
lean_inc_ref(v_inst_890_);
v___x_897_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_897_, 0, v_inst_890_);
lean_closure_set(v___x_897_, 1, v_fn_891_);
v_sz_898_ = lean_array_size(v_args_892_);
v___x_899_ = ((size_t)0ULL);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_890_, v___x_897_, v_sz_898_, v___x_899_, v_args_892_);
v___x_901_ = lean_apply_4(v_toBind_893_, lean_box(0), lean_box(0), v___x_900_, v___f_894_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_903_; 
lean_dec(v___f_894_);
lean_dec(v_toBind_893_);
lean_dec_ref(v_args_892_);
lean_dec(v_fn_891_);
lean_dec_ref(v_inst_890_);
v_val_902_ = lean_ctor_get(v_____do__lift_896_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v_____do__lift_896_, 1);
v___x_903_ = lean_apply_2(v_toPure_895_, lean_box(0), v_val_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_904_, lean_object* v_inst_905_, lean_object* v_fn_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Syntax_replaceM___redArg(v_inst_905_, v_fn_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_909_, lean_object* v_kind_910_, lean_object* v_fn_911_, lean_object* v_args_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_913_, 0, v_info_909_);
lean_ctor_set(v___x_913_, 1, v_kind_910_);
lean_ctor_set(v___x_913_, 2, v_args_912_);
v___x_914_ = lean_apply_1(v_fn_911_, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_915_, lean_object* v_fn_916_, lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_917_) == 1)
{
lean_object* v_toBind_918_; lean_object* v_info_919_; lean_object* v_kind_920_; lean_object* v_args_921_; lean_object* v___f_922_; lean_object* v___x_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_toBind_918_ = lean_ctor_get(v_inst_915_, 1);
lean_inc(v_toBind_918_);
v_info_919_ = lean_ctor_get(v_x_917_, 0);
lean_inc(v_info_919_);
v_kind_920_ = lean_ctor_get(v_x_917_, 1);
lean_inc(v_kind_920_);
v_args_921_ = lean_ctor_get(v_x_917_, 2);
lean_inc_ref(v_args_921_);
lean_dec_ref_known(v_x_917_, 3);
lean_inc(v_fn_916_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_922_, 0, v_info_919_);
lean_closure_set(v___f_922_, 1, v_kind_920_);
lean_closure_set(v___f_922_, 2, v_fn_916_);
lean_inc_ref(v_inst_915_);
v___x_923_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_923_, 0, v_inst_915_);
lean_closure_set(v___x_923_, 1, v_fn_916_);
v_sz_924_ = lean_array_size(v_args_921_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_915_, v___x_923_, v_sz_924_, v___x_925_, v_args_921_);
v___x_927_ = lean_apply_4(v_toBind_918_, lean_box(0), lean_box(0), v___x_926_, v___f_922_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; 
lean_dec_ref(v_inst_915_);
v___x_928_ = lean_apply_1(v_fn_916_, v_x_917_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_929_, lean_object* v_inst_930_, lean_object* v_fn_931_, lean_object* v_x_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_930_, v_fn_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_934_, lean_object* v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = lean_apply_1(v_fn_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_956_, lean_object* v_stx_957_){
_start:
{
lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_958_, 0, v_fn_956_);
v___x_959_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_960_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_959_, v___f_958_, v_stx_957_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_961_) == 0)
{
lean_object* v_leading_964_; lean_object* v_trailing_965_; lean_object* v_pos_966_; lean_object* v_endPos_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_994_; 
v_leading_964_ = lean_ctor_get(v_x_961_, 0);
v_trailing_965_ = lean_ctor_get(v_x_961_, 2);
v_pos_966_ = lean_ctor_get(v_x_961_, 1);
v_endPos_967_ = lean_ctor_get(v_x_961_, 3);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_961_);
if (v_isSharedCheck_994_ == 0)
{
v___x_969_ = v_x_961_;
v_isShared_970_ = v_isSharedCheck_994_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_endPos_967_);
lean_inc(v_trailing_965_);
lean_inc(v_pos_966_);
lean_inc(v_leading_964_);
lean_dec(v_x_961_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_994_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_str_971_; lean_object* v_stopPos_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_992_; 
v_str_971_ = lean_ctor_get(v_leading_964_, 0);
v_stopPos_972_ = lean_ctor_get(v_leading_964_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_leading_964_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_leading_964_, 1);
lean_dec(v_unused_993_);
v___x_974_ = v_leading_964_;
v_isShared_975_ = v_isSharedCheck_992_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_stopPos_972_);
lean_inc(v_str_971_);
lean_dec(v_leading_964_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_992_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_str_976_; lean_object* v_startPos_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_990_; 
v_str_976_ = lean_ctor_get(v_trailing_965_, 0);
v_startPos_977_ = lean_ctor_get(v_trailing_965_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_trailing_965_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_trailing_965_, 2);
lean_dec(v_unused_991_);
v___x_979_ = v_trailing_965_;
v_isShared_980_ = v_isSharedCheck_990_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_startPos_977_);
lean_inc(v_str_976_);
lean_dec(v_trailing_965_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_990_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 2, v_stopPos_972_);
lean_ctor_set(v___x_979_, 1, v_x_962_);
lean_ctor_set(v___x_979_, 0, v_str_971_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_str_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_x_962_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_stopPos_972_);
v___x_982_ = v_reuseFailAlloc_989_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 2, v_x_963_);
lean_ctor_set(v___x_974_, 1, v_startPos_977_);
lean_ctor_set(v___x_974_, 0, v_str_976_);
v___x_984_ = v___x_974_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_str_976_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_startPos_977_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_x_963_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 2, v___x_984_);
lean_ctor_set(v___x_969_, 0, v___x_982_);
v___x_986_ = v___x_969_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_pos_966_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_endPos_967_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_963_);
lean_dec(v_x_962_);
return v_x_961_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_a_998_, lean_object* v_b_999_){
_start:
{
lean_object* v___x_1000_; uint8_t v_decide_1001_; 
v___x_1000_ = lean_nat_sub(v___x_995_, v___x_996_);
v_decide_1001_ = lean_nat_dec_eq(v_a_998_, v___x_1000_);
lean_dec(v___x_1000_);
if (v_decide_1001_ == 0)
{
uint32_t v___x_1002_; lean_object* v___x_1003_; uint32_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1002_ = 10;
v___x_1003_ = lean_nat_add(v___x_996_, v_a_998_);
v___x_1004_ = lean_string_utf8_get_fast(v___x_997_, v___x_1003_);
v___x_1005_ = lean_uint32_dec_eq(v___x_1004_, v___x_1002_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_a_998_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_string_utf8_next_fast(v___x_997_, v___x_1003_);
lean_dec(v___x_1003_);
v___x_1008_ = lean_nat_sub(v___x_1007_, v___x_996_);
v_a_998_ = v___x_1008_;
v_b_999_ = v___x_1006_;
goto _start;
}
else
{
lean_object* v___x_1010_; 
lean_dec(v___x_1003_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_a_998_);
return v___x_1010_;
}
}
else
{
lean_dec(v_a_998_);
lean_inc(v_b_999_);
return v_b_999_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1011_, v___x_1012_, v___x_1013_, v_a_1014_, v_b_1015_);
lean_dec(v_b_1015_);
lean_dec_ref(v___x_1013_);
lean_dec(v___x_1012_);
lean_dec(v___x_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_1017_){
_start:
{
lean_object* v_str_1018_; lean_object* v_startPos_1019_; lean_object* v_stopPos_1020_; uint8_t v___y_1022_; uint8_t v___x_1032_; 
v_str_1018_ = lean_ctor_get(v_trail_1017_, 0);
v_startPos_1019_ = lean_ctor_get(v_trail_1017_, 1);
v_stopPos_1020_ = lean_ctor_get(v_trail_1017_, 2);
v___x_1032_ = lean_string_is_valid_pos(v_str_1018_, v_startPos_1019_);
if (v___x_1032_ == 0)
{
v___y_1022_ = v___x_1032_;
goto v___jp_1021_;
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_string_is_valid_pos(v_str_1018_, v_stopPos_1020_);
if (v___x_1033_ == 0)
{
v___y_1022_ = v___x_1033_;
goto v___jp_1021_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_le(v_startPos_1019_, v_stopPos_1020_);
v___y_1022_ = v___x_1034_;
goto v___jp_1021_;
}
}
v___jp_1021_:
{
if (v___y_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_nat_sub(v_stopPos_1020_, v_startPos_1019_);
v___x_1024_ = lean_nat_add(v_startPos_1019_, v___x_1023_);
lean_dec(v___x_1023_);
return v___x_1024_;
}
else
{
lean_object* v_searcher_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_searcher_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_box(0);
v___x_1027_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v_stopPos_1020_, v_startPos_1019_, v_str_1018_, v_searcher_1025_, v___x_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_nat_sub(v_stopPos_1020_, v_startPos_1019_);
v___x_1029_ = lean_nat_add(v_startPos_1019_, v___x_1028_);
lean_dec(v___x_1028_);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
v_val_1030_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1031_ = lean_nat_add(v_startPos_1019_, v_val_1030_);
lean_dec(v_val_1030_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object* v_trail_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trail_1035_);
lean_dec_ref(v_trail_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_inst_1041_, lean_object* v_R_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v_c_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1037_, v___x_1038_, v___x_1040_, v_a_1043_, v_b_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_inst_1051_, lean_object* v_R_1052_, lean_object* v_a_1053_, lean_object* v_b_1054_, lean_object* v_c_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1047_, v___x_1048_, v___x_1049_, v___x_1050_, v_inst_1051_, v_R_1052_, v_a_1053_, v_b_1054_, v_c_1055_);
lean_dec(v_b_1054_);
lean_dec_ref(v___x_1050_);
lean_dec_ref(v___x_1049_);
lean_dec(v___x_1048_);
lean_dec(v___x_1047_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___y_1060_; 
switch(lean_obj_tag(v_x_1057_))
{
case 2:
{
lean_object* v_info_1063_; 
v_info_1063_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_info_1063_);
if (lean_obj_tag(v_info_1063_) == 0)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1076_; 
v_val_1064_ = lean_ctor_get(v_x_1057_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_x_1057_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_x_1057_, 0);
lean_dec(v_unused_1077_);
v___x_1066_ = v_x_1057_;
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v_x_1057_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_trailing_1068_; lean_object* v_trailStop_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_trailing_1068_ = lean_ctor_get(v_info_1063_, 2);
v_trailStop_1069_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1068_);
lean_inc(v_trailStop_1069_);
v___x_1070_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1063_, v_a_1058_, v_trailStop_1069_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_val_1064_);
v___x_1072_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_trailStop_1069_);
return v___x_1074_;
}
}
}
else
{
lean_dec_ref_known(v_x_1057_, 2);
lean_dec(v_info_1063_);
v___y_1060_ = v_a_1058_;
goto v___jp_1059_;
}
}
case 3:
{
lean_object* v_info_1078_; 
v_info_1078_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_info_1078_);
if (lean_obj_tag(v_info_1078_) == 0)
{
lean_object* v_rawVal_1079_; lean_object* v_val_1080_; lean_object* v_preresolved_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1093_; 
v_rawVal_1079_ = lean_ctor_get(v_x_1057_, 1);
v_val_1080_ = lean_ctor_get(v_x_1057_, 2);
v_preresolved_1081_ = lean_ctor_get(v_x_1057_, 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_1057_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_x_1057_, 0);
lean_dec(v_unused_1094_);
v___x_1083_ = v_x_1057_;
v_isShared_1084_ = v_isSharedCheck_1093_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_preresolved_1081_);
lean_inc(v_val_1080_);
lean_inc(v_rawVal_1079_);
lean_dec(v_x_1057_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1093_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_trailing_1085_; lean_object* v_trailStop_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v_trailing_1085_ = lean_ctor_get(v_info_1078_, 2);
v_trailStop_1086_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1085_);
lean_inc(v_trailStop_1086_);
v___x_1087_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1078_, v_a_1058_, v_trailStop_1086_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1087_);
v___x_1089_ = v___x_1083_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_rawVal_1079_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_val_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_preresolved_1081_);
v___x_1089_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_trailStop_1086_);
return v___x_1091_;
}
}
}
else
{
lean_dec_ref_known(v_x_1057_, 4);
lean_dec(v_info_1078_);
v___y_1060_ = v_a_1058_;
goto v___jp_1059_;
}
}
default: 
{
lean_dec(v_x_1057_);
v___y_1060_ = v_a_1058_;
goto v___jp_1059_;
}
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___y_1060_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
switch(lean_obj_tag(v___y_1095_))
{
case 2:
{
lean_object* v_info_1100_; 
v_info_1100_ = lean_ctor_get(v___y_1095_, 0);
lean_inc(v_info_1100_);
if (lean_obj_tag(v_info_1100_) == 0)
{
lean_object* v_val_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1113_; 
v_val_1101_ = lean_ctor_get(v___y_1095_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___y_1095_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___y_1095_, 0);
lean_dec(v_unused_1114_);
v___x_1103_ = v___y_1095_;
v_isShared_1104_ = v_isSharedCheck_1113_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_val_1101_);
lean_dec(v___y_1095_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1113_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_trailing_1105_; lean_object* v_trailStop_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v_trailing_1105_ = lean_ctor_get(v_info_1100_, 2);
v_trailStop_1106_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1105_);
lean_inc(v_trailStop_1106_);
v___x_1107_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1100_, v___y_1096_, v_trailStop_1106_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1107_);
v___x_1109_ = v___x_1103_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_val_1101_);
v___x_1109_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_trailStop_1106_);
return v___x_1111_;
}
}
}
else
{
lean_dec_ref_known(v___y_1095_, 2);
lean_dec(v_info_1100_);
goto v___jp_1097_;
}
}
case 3:
{
lean_object* v_info_1115_; 
v_info_1115_ = lean_ctor_get(v___y_1095_, 0);
lean_inc(v_info_1115_);
if (lean_obj_tag(v_info_1115_) == 0)
{
lean_object* v_rawVal_1116_; lean_object* v_val_1117_; lean_object* v_preresolved_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1130_; 
v_rawVal_1116_ = lean_ctor_get(v___y_1095_, 1);
v_val_1117_ = lean_ctor_get(v___y_1095_, 2);
v_preresolved_1118_ = lean_ctor_get(v___y_1095_, 3);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___y_1095_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___y_1095_, 0);
lean_dec(v_unused_1131_);
v___x_1120_ = v___y_1095_;
v_isShared_1121_ = v_isSharedCheck_1130_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_preresolved_1118_);
lean_inc(v_val_1117_);
lean_inc(v_rawVal_1116_);
lean_dec(v___y_1095_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1130_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_trailing_1122_; lean_object* v_trailStop_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v_trailing_1122_ = lean_ctor_get(v_info_1115_, 2);
v_trailStop_1123_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1122_);
lean_inc(v_trailStop_1123_);
v___x_1124_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1115_, v___y_1096_, v_trailStop_1123_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1124_);
v___x_1126_ = v___x_1120_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_rawVal_1116_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_val_1117_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_preresolved_1118_);
v___x_1126_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_trailStop_1123_);
return v___x_1128_;
}
}
}
else
{
lean_dec(v_info_1115_);
lean_dec_ref_known(v___y_1095_, 4);
goto v___jp_1097_;
}
}
default: 
{
lean_dec(v___y_1095_);
goto v___jp_1097_;
}
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___y_1096_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1132_, lean_object* v___y_1133_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 1)
{
lean_object* v_info_1134_; lean_object* v_kind_1135_; lean_object* v_args_1136_; lean_object* v___x_1137_; lean_object* v_fst_1138_; 
v_info_1134_ = lean_ctor_get(v_x_1132_, 0);
lean_inc(v_info_1134_);
v_kind_1135_ = lean_ctor_get(v_x_1132_, 1);
lean_inc(v_kind_1135_);
v_args_1136_ = lean_ctor_get(v_x_1132_, 2);
lean_inc_ref(v_args_1136_);
v___x_1137_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1132_, v___y_1133_);
v_fst_1138_ = lean_ctor_get(v___x_1137_, 0);
if (lean_obj_tag(v_fst_1138_) == 0)
{
lean_object* v_snd_1139_; size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_snd_1139_ = lean_ctor_get(v___x_1137_, 1);
lean_inc(v_snd_1139_);
lean_dec_ref(v___x_1137_);
v_sz_1140_ = lean_array_size(v_args_1136_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1140_, v___x_1141_, v_args_1136_, v_snd_1139_);
v_fst_1143_ = lean_ctor_get(v___x_1142_, 0);
v_snd_1144_ = lean_ctor_get(v___x_1142_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v___x_1142_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
lean_dec(v___x_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1148_, 0, v_info_1134_);
lean_ctor_set(v___x_1148_, 1, v_kind_1135_);
lean_ctor_set(v___x_1148_, 2, v_fst_1143_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_snd_1144_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_snd_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
lean_inc_ref(v_fst_1138_);
lean_dec_ref(v_args_1136_);
lean_dec(v_kind_1135_);
lean_dec(v_info_1134_);
v_snd_1153_ = lean_ctor_get(v___x_1137_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v___x_1137_, 0);
lean_dec(v_unused_1162_);
v___x_1155_ = v___x_1137_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snd_1153_);
lean_dec(v___x_1137_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_val_1157_; lean_object* v___x_1159_; 
v_val_1157_ = lean_ctor_get(v_fst_1138_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v_fst_1138_, 1);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v_val_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_val_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_snd_1153_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v_fst_1164_; 
lean_inc(v_x_1132_);
v___x_1163_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1132_, v___y_1133_);
v_fst_1164_ = lean_ctor_get(v___x_1163_, 0);
if (lean_obj_tag(v_fst_1164_) == 0)
{
lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_snd_1165_ = lean_ctor_get(v___x_1163_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v___x_1163_, 0);
lean_dec(v_unused_1173_);
v___x_1167_ = v___x_1163_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_dec(v___x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v_x_1132_);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_x_1132_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_snd_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_snd_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
lean_inc_ref(v_fst_1164_);
lean_dec(v_x_1132_);
v_snd_1174_ = lean_ctor_get(v___x_1163_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1163_, 0);
lean_dec(v_unused_1183_);
v___x_1176_ = v___x_1163_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snd_1174_);
lean_dec(v___x_1163_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_val_1178_; lean_object* v___x_1180_; 
v_val_1178_ = lean_ctor_get(v_fst_1164_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v_fst_1164_, 1);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v_val_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_val_1178_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_snd_1174_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_bs_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_lt(v_i_1185_, v_sz_1184_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_bs_1186_);
lean_ctor_set(v___x_1189_, 1, v___y_1187_);
return v___x_1189_;
}
else
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1194_; lean_object* v_bs_x27_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v_v_1190_ = lean_array_uget_borrowed(v_bs_1186_, v_i_1185_);
lean_inc(v_v_1190_);
v___x_1191_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1190_, v___y_1187_);
v_fst_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_fst_1192_);
v_snd_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_snd_1193_);
lean_dec_ref(v___x_1191_);
v___x_1194_ = lean_unsigned_to_nat(0u);
v_bs_x27_1195_ = lean_array_uset(v_bs_1186_, v_i_1185_, v___x_1194_);
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_add(v_i_1185_, v___x_1196_);
v___x_1198_ = lean_array_uset(v_bs_x27_1195_, v_i_1185_, v_fst_1192_);
v_i_1185_ = v___x_1197_;
v_bs_1186_ = v___x_1198_;
v___y_1187_ = v_snd_1193_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1184_ = stack[0].m_num;
size_t v_i_1185_ = stack[1].m_num;
lean_object* v_bs_1186_ = stack[2].m_obj;
lean_object* v___y_1187_ = stack[3].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1184_, v_i_1185_, v_bs_1186_, v___y_1187_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1201_, lean_object* v_i_1202_, lean_object* v_bs_1203_, lean_object* v___y_1204_){
_start:
{
size_t v_sz_boxed_1205_; size_t v_i_boxed_1206_; lean_object* v_res_1207_; 
v_sz_boxed_1205_ = lean_unbox_usize(v_sz_1201_);
lean_dec(v_sz_1201_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1202_);
lean_dec(v_i_1202_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1205_, v_i_boxed_1206_, v_bs_1203_, v___y_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_fst_1211_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1208_, v___x_1209_);
v_fst_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_fst_1211_);
lean_dec_ref(v___x_1210_);
return v_fst_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1212_, lean_object* v_x_1213_){
_start:
{
switch(lean_obj_tag(v_x_1213_))
{
case 2:
{
lean_object* v_info_1214_; lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_info_1214_ = lean_ctor_get(v_x_1213_, 0);
v_val_1215_ = lean_ctor_get(v_x_1213_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_x_1213_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_inc(v_info_1214_);
lean_dec(v_x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1212_, v_info_1214_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_val_1215_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
case 3:
{
lean_object* v_info_1224_; lean_object* v_rawVal_1225_; lean_object* v_val_1226_; lean_object* v_preresolved_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_info_1224_ = lean_ctor_get(v_x_1213_, 0);
v_rawVal_1225_ = lean_ctor_get(v_x_1213_, 1);
v_val_1226_ = lean_ctor_get(v_x_1213_, 2);
v_preresolved_1227_ = lean_ctor_get(v_x_1213_, 3);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v_x_1213_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_preresolved_1227_);
lean_inc(v_val_1226_);
lean_inc(v_rawVal_1225_);
lean_inc(v_info_1224_);
lean_dec(v_x_1213_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1212_, v_info_1224_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_rawVal_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_val_1226_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_preresolved_1227_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
case 1:
{
lean_object* v_info_1236_; lean_object* v_kind_1237_; lean_object* v_args_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_info_1236_ = lean_ctor_get(v_x_1213_, 0);
v_kind_1237_ = lean_ctor_get(v_x_1213_, 1);
v_args_1238_ = lean_ctor_get(v_x_1213_, 2);
v___x_1239_ = lean_array_get_size(v_args_1238_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_nat_dec_eq(v___x_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1253_; 
lean_inc_ref(v_args_1238_);
lean_inc(v_kind_1237_);
lean_inc(v_info_1236_);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; lean_object* v_unused_1255_; lean_object* v_unused_1256_; 
v_unused_1254_ = lean_ctor_get(v_x_1213_, 2);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_x_1213_, 1);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_x_1213_, 0);
lean_dec(v_unused_1256_);
v___x_1243_ = v_x_1213_;
v_isShared_1244_ = v_isSharedCheck_1253_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v_x_1213_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1253_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v_i_1246_; lean_object* v___x_1247_; lean_object* v_last_1248_; lean_object* v_args_1249_; lean_object* v___x_1251_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v_i_1246_ = lean_nat_sub(v___x_1239_, v___x_1245_);
v___x_1247_ = lean_array_fget_borrowed(v_args_1238_, v_i_1246_);
lean_inc(v___x_1247_);
v_last_1248_ = l_Lean_Syntax_updateTrailing(v_trailing_1212_, v___x_1247_);
v_args_1249_ = lean_array_fset(v_args_1238_, v_i_1246_, v_last_1248_);
lean_dec(v_i_1246_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 2, v_args_1249_);
v___x_1251_ = v___x_1243_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_info_1236_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_kind_1237_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_args_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
else
{
lean_dec_ref(v_trailing_1212_);
return v_x_1213_;
}
}
default: 
{
lean_dec_ref(v_trailing_1212_);
return v_x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
return v_x_1257_;
}
else
{
lean_object* v_head_1259_; lean_object* v_tail_1260_; lean_object* v___x_1261_; 
v_head_1259_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_head_1259_);
v_tail_1260_ = lean_ctor_get(v_x_1258_, 1);
lean_inc(v_tail_1260_);
lean_dec_ref_known(v_x_1258_, 2);
v___x_1261_ = l_Lean_Name_append(v_x_1257_, v_head_1259_);
v_x_1257_ = v___x_1261_;
v_x_1258_ = v_tail_1260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1265_, lean_object* v_nFields_x3f_1266_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1266_) == 1)
{
lean_object* v_val_1267_; lean_object* v_nameComps_1268_; lean_object* v___x_1269_; lean_object* v_nPrefix_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_namePrefix_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_val_1267_ = lean_ctor_get(v_nFields_x3f_1266_, 0);
v_nameComps_1268_ = l_Lean_Name_components(v_n_1265_);
v___x_1269_ = l_List_lengthTR___redArg(v_nameComps_1268_);
v_nPrefix_1270_ = lean_nat_sub(v___x_1269_, v_val_1267_);
lean_dec(v___x_1269_);
v___x_1271_ = lean_box(0);
v___x_1272_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1270_);
lean_inc(v_nameComps_1268_);
v___x_1273_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1268_, v_nameComps_1268_, v_nPrefix_1270_, v___x_1272_);
v_namePrefix_1274_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1271_, v___x_1273_);
v___x_1275_ = l_List_drop___redArg(v_nPrefix_1270_, v_nameComps_1268_);
lean_dec(v_nameComps_1268_);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_namePrefix_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Name_components(v_n_1265_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1278_, lean_object* v_nFields_x3f_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1278_, v_nFields_x3f_1279_);
lean_dec(v_nFields_x3f_1279_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_panic_fn_borrowed(v___x_1282_, v_msg_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
return v_x_1284_;
}
else
{
lean_object* v_head_1286_; lean_object* v_tail_1287_; lean_object* v_startPos_1288_; lean_object* v_stopPos_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_head_1286_ = lean_ctor_get(v_x_1285_, 0);
v_tail_1287_ = lean_ctor_get(v_x_1285_, 1);
v_startPos_1288_ = lean_ctor_get(v_head_1286_, 1);
v_stopPos_1289_ = lean_ctor_get(v_head_1286_, 2);
v___x_1290_ = lean_nat_sub(v_stopPos_1289_, v_startPos_1288_);
v___x_1291_ = lean_nat_add(v_x_1284_, v___x_1290_);
lean_dec(v___x_1290_);
lean_dec(v_x_1284_);
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_nat_add(v___x_1291_, v___x_1292_);
lean_dec(v___x_1291_);
v_x_1284_ = v___x_1293_;
v_x_1285_ = v_tail_1287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1295_, v_x_1296_);
lean_dec(v_x_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1302_, lean_object* v_pos_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
if (lean_obj_tag(v_a_1304_) == 0)
{
lean_object* v___x_1306_; 
v___x_1306_ = l_List_reverse___redArg(v_a_1305_);
return v___x_1306_;
}
else
{
lean_object* v_head_1307_; lean_object* v_tail_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1326_; 
v_head_1307_ = lean_ctor_get(v_a_1304_, 0);
v_tail_1308_ = lean_ctor_get(v_a_1304_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_a_1304_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1310_ = v_a_1304_;
v_isShared_1311_ = v_isSharedCheck_1326_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_tail_1308_);
lean_inc(v_head_1307_);
lean_dec(v_a_1304_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1326_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_stopPos_1312_; lean_object* v_startPos_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_info_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v_stopPos_1312_ = lean_ctor_get(v_head_1307_, 2);
lean_inc(v_stopPos_1312_);
lean_dec(v_head_1307_);
v_startPos_1313_ = lean_ctor_get(v_rawVal_1302_, 1);
v___x_1314_ = lean_nat_sub(v_stopPos_1312_, v_startPos_1313_);
lean_dec(v_stopPos_1312_);
v___x_1315_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1316_ = lean_nat_add(v___x_1314_, v_pos_1303_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_add(v___x_1317_, v___x_1316_);
v_info_1319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1319_, 0, v___x_1315_);
lean_ctor_set(v_info_1319_, 1, v___x_1316_);
lean_ctor_set(v_info_1319_, 2, v___x_1315_);
lean_ctor_set(v_info_1319_, 3, v___x_1318_);
v___x_1320_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_info_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v_a_1305_);
lean_ctor_set(v___x_1310_, 0, v___x_1321_);
v___x_1323_ = v___x_1310_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_a_1305_);
v___x_1323_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v_a_1304_ = v_tail_1308_;
v_a_1305_ = v___x_1323_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1327_, lean_object* v_pos_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1327_, v_pos_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_pos_1328_);
lean_dec_ref(v_rawVal_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1332_, lean_object* v_pos_1333_, lean_object* v_trailing_1334_, lean_object* v_leading_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
if (lean_obj_tag(v_a_1336_) == 0)
{
lean_object* v___x_1338_; 
lean_dec_ref(v_leading_1335_);
lean_dec_ref(v_trailing_1334_);
v___x_1338_ = l_List_reverse___redArg(v_a_1337_);
return v___x_1338_;
}
else
{
lean_object* v_head_1339_; lean_object* v_snd_1340_; lean_object* v_tail_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1371_; 
v_head_1339_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_head_1339_);
v_snd_1340_ = lean_ctor_get(v_head_1339_, 1);
lean_inc(v_snd_1340_);
v_tail_1341_ = lean_ctor_get(v_a_1336_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1336_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_a_1336_, 0);
lean_dec(v_unused_1372_);
v___x_1343_ = v_a_1336_;
v_isShared_1344_ = v_isSharedCheck_1371_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_tail_1341_);
lean_dec(v_a_1336_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1371_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_fst_1345_; lean_object* v_startPos_1346_; lean_object* v_stopPos_1347_; lean_object* v_startPos_1348_; lean_object* v_stopPos_1349_; lean_object* v_off_1350_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1365_; lean_object* v___x_1368_; uint8_t v_decide_1369_; 
v_fst_1345_ = lean_ctor_get(v_head_1339_, 0);
lean_inc(v_fst_1345_);
lean_dec(v_head_1339_);
v_startPos_1346_ = lean_ctor_get(v_snd_1340_, 1);
v_stopPos_1347_ = lean_ctor_get(v_snd_1340_, 2);
v_startPos_1348_ = lean_ctor_get(v_rawVal_1332_, 1);
v_stopPos_1349_ = lean_ctor_get(v_rawVal_1332_, 2);
v_off_1350_ = lean_nat_sub(v_startPos_1346_, v_startPos_1348_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v_decide_1369_ = lean_nat_dec_eq(v_off_1350_, v___x_1368_);
if (v_decide_1369_ == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1365_ = v___x_1370_;
goto v___jp_1364_;
}
else
{
lean_inc_ref(v_leading_1335_);
v___y_1365_ = v_leading_1335_;
goto v___jp_1364_;
}
v___jp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_info_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1354_ = lean_nat_add(v_off_1350_, v_pos_1333_);
lean_dec(v_off_1350_);
v___x_1355_ = lean_nat_sub(v_stopPos_1347_, v_startPos_1346_);
v___x_1356_ = lean_nat_add(v___x_1355_, v___x_1354_);
lean_dec(v___x_1355_);
v_info_1357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1357_, 0, v___y_1352_);
lean_ctor_set(v_info_1357_, 1, v___x_1354_);
lean_ctor_set(v_info_1357_, 2, v___y_1353_);
lean_ctor_set(v_info_1357_, 3, v___x_1356_);
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1359_, 0, v_info_1357_);
lean_ctor_set(v___x_1359_, 1, v_snd_1340_);
lean_ctor_set(v___x_1359_, 2, v_fst_1345_);
lean_ctor_set(v___x_1359_, 3, v___x_1358_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v_a_1337_);
lean_ctor_set(v___x_1343_, 0, v___x_1359_);
v___x_1361_ = v___x_1343_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1337_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v_a_1336_ = v_tail_1341_;
v_a_1337_ = v___x_1361_;
goto _start;
}
}
v___jp_1364_:
{
uint8_t v_decide_1366_; 
v_decide_1366_ = lean_nat_dec_eq(v_stopPos_1347_, v_stopPos_1349_);
if (v_decide_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1352_ = v___y_1365_;
v___y_1353_ = v___x_1367_;
goto v___jp_1351_;
}
else
{
lean_inc_ref(v_trailing_1334_);
v___y_1352_ = v___y_1365_;
v___y_1353_ = v_trailing_1334_;
goto v___jp_1351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1373_, lean_object* v_pos_1374_, lean_object* v_trailing_1375_, lean_object* v_leading_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1373_, v_pos_1374_, v_trailing_1375_, v_leading_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_pos_1374_);
lean_dec_ref(v_rawVal_1373_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__4(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1385_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1386_ = lean_unsigned_to_nat(9u);
v___x_1387_ = lean_unsigned_to_nat(342u);
v___x_1388_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1389_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1390_ = l_mkPanicMessageWithDecl(v___x_1389_, v___x_1388_, v___x_1387_, v___x_1386_, v___x_1385_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1391_, lean_object* v_nFields_x3f_1392_){
_start:
{
if (lean_obj_tag(v_stx_1391_) == 3)
{
lean_object* v_info_1393_; 
v_info_1393_ = lean_ctor_get(v_stx_1391_, 0);
lean_inc(v_info_1393_);
if (lean_obj_tag(v_info_1393_) == 0)
{
lean_object* v_rawVal_1394_; lean_object* v_val_1395_; lean_object* v_leading_1396_; lean_object* v_pos_1397_; lean_object* v_trailing_1398_; lean_object* v_rawComps_1399_; uint8_t v___x_1400_; 
v_rawVal_1394_ = lean_ctor_get(v_stx_1391_, 1);
lean_inc_ref_n(v_rawVal_1394_, 2);
v_val_1395_ = lean_ctor_get(v_stx_1391_, 2);
lean_inc(v_val_1395_);
lean_dec_ref_known(v_stx_1391_, 4);
v_leading_1396_ = lean_ctor_get(v_info_1393_, 0);
lean_inc_ref(v_leading_1396_);
v_pos_1397_ = lean_ctor_get(v_info_1393_, 1);
lean_inc(v_pos_1397_);
v_trailing_1398_ = lean_ctor_get(v_info_1393_, 2);
lean_inc_ref(v_trailing_1398_);
lean_dec_ref_known(v_info_1393_, 4);
v_rawComps_1399_ = l_Lean_Syntax_splitNameLit(v_rawVal_1394_);
v___x_1400_ = l_List_isEmpty___redArg(v_rawComps_1399_);
if (v___x_1400_ == 0)
{
lean_object* v_val_1401_; lean_object* v_nameComps_1402_; lean_object* v___y_1404_; 
v_val_1401_ = l_Lean_Name_eraseMacroScopes(v_val_1395_);
lean_dec(v_val_1395_);
v_nameComps_1402_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1401_, v_nFields_x3f_1392_);
if (lean_obj_tag(v_nFields_x3f_1392_) == 1)
{
lean_object* v_val_1418_; lean_object* v_str_1419_; lean_object* v_startPos_1420_; lean_object* v_stopPos_1421_; lean_object* v___x_1422_; lean_object* v_nPrefix_1423_; lean_object* v___y_1425_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_prefixSz_1431_; lean_object* v___x_1432_; lean_object* v_prefixSz_1433_; lean_object* v___y_1435_; uint8_t v___x_1440_; 
v_val_1418_ = lean_ctor_get(v_nFields_x3f_1392_, 0);
v_str_1419_ = lean_ctor_get(v_rawVal_1394_, 0);
v_startPos_1420_ = lean_ctor_get(v_rawVal_1394_, 1);
v_stopPos_1421_ = lean_ctor_get(v_rawVal_1394_, 2);
v___x_1422_ = l_List_lengthTR___redArg(v_rawComps_1399_);
v_nPrefix_1423_ = lean_nat_sub(v___x_1422_, v_val_1418_);
lean_dec(v___x_1422_);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1423_);
lean_inc(v_rawComps_1399_);
v___x_1430_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1399_, v_rawComps_1399_, v_nPrefix_1423_, v___x_1429_);
v_prefixSz_1431_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1428_, v___x_1430_);
lean_dec(v___x_1430_);
v___x_1432_ = lean_unsigned_to_nat(1u);
v_prefixSz_1433_ = lean_nat_sub(v_prefixSz_1431_, v___x_1432_);
lean_dec(v_prefixSz_1431_);
v___x_1440_ = lean_nat_dec_le(v_prefixSz_1433_, v___x_1428_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_le(v_stopPos_1421_, v_startPos_1420_);
if (v___x_1441_ == 0)
{
lean_inc(v_startPos_1420_);
v___y_1435_ = v_startPos_1420_;
goto v___jp_1434_;
}
else
{
lean_inc(v_stopPos_1421_);
v___y_1435_ = v_stopPos_1421_;
goto v___jp_1434_;
}
}
else
{
lean_object* v___x_1442_; 
lean_dec(v_prefixSz_1433_);
v___x_1442_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1425_ = v___x_1442_;
goto v___jp_1424_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = l_List_drop___redArg(v_nPrefix_1423_, v_rawComps_1399_);
lean_dec(v_rawComps_1399_);
v___x_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___y_1404_ = v___x_1427_;
goto v___jp_1403_;
}
v___jp_1434_:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_nat_add(v_startPos_1420_, v_prefixSz_1433_);
lean_dec(v_prefixSz_1433_);
v___x_1437_ = lean_nat_dec_le(v_stopPos_1421_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_inc_ref(v_str_1419_);
v___x_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1438_, 0, v_str_1419_);
lean_ctor_set(v___x_1438_, 1, v___y_1435_);
lean_ctor_set(v___x_1438_, 2, v___x_1436_);
v___y_1425_ = v___x_1438_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1439_; 
lean_dec(v___x_1436_);
lean_inc(v_stopPos_1421_);
lean_inc_ref(v_str_1419_);
v___x_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1439_, 0, v_str_1419_);
lean_ctor_set(v___x_1439_, 1, v___y_1435_);
lean_ctor_set(v___x_1439_, 2, v_stopPos_1421_);
v___y_1425_ = v___x_1439_;
goto v___jp_1424_;
}
}
}
else
{
v___y_1404_ = v_rawComps_1399_;
goto v___jp_1403_;
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = l_List_lengthTR___redArg(v_nameComps_1402_);
v___x_1406_ = l_List_lengthTR___redArg(v___y_1404_);
v___x_1407_ = lean_nat_dec_eq(v___x_1405_, v___x_1406_);
lean_dec(v___x_1406_);
lean_dec(v___x_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_dec(v___y_1404_);
lean_dec(v_nameComps_1402_);
lean_dec_ref(v_trailing_1398_);
lean_dec(v_pos_1397_);
lean_dec_ref(v_leading_1396_);
lean_dec_ref(v_rawVal_1394_);
v___x_1408_ = lean_box(0);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_comps_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_seps_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_inc(v___y_1404_);
v___x_1409_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1402_, v___y_1404_);
v___x_1410_ = lean_box(0);
v_comps_1411_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1394_, v_pos_1397_, v_trailing_1398_, v_leading_1396_, v___x_1409_, v___x_1410_);
v___x_1412_ = lean_array_mk(v___y_1404_);
v___x_1413_ = lean_array_pop(v___x_1412_);
v___x_1414_ = lean_array_to_list(v___x_1413_);
v_seps_1415_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1394_, v_pos_1397_, v___x_1414_, v___x_1410_);
lean_dec(v_pos_1397_);
lean_dec_ref(v_rawVal_1394_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_comps_1411_);
lean_ctor_set(v___x_1416_, 1, v_seps_1415_);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
}
else
{
lean_object* v___x_1443_; 
lean_dec(v_rawComps_1399_);
lean_dec_ref(v_trailing_1398_);
lean_dec(v_pos_1397_);
lean_dec_ref(v_leading_1396_);
lean_dec(v_val_1395_);
lean_dec_ref(v_rawVal_1394_);
v___x_1443_ = lean_box(0);
return v___x_1443_;
}
}
else
{
lean_object* v___x_1444_; 
lean_dec(v_info_1393_);
lean_dec_ref_known(v_stx_1391_, 4);
v___x_1444_ = lean_box(0);
return v___x_1444_;
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v_stx_1391_);
v___x_1445_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__4, &l_Lean_Syntax_identComponents_x3f___closed__4_once, _init_l_Lean_Syntax_identComponents_x3f___closed__4);
v___x_1446_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1445_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1447_, lean_object* v_nFields_x3f_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Syntax_identComponents_x3f(v_stx_1447_, v_nFields_x3f_1448_);
lean_dec(v_nFields_x3f_1448_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1450_, lean_object* v_nFields_x3f_1451_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1451_) == 1)
{
lean_object* v_val_1452_; lean_object* v_nameComps_1453_; lean_object* v___x_1454_; lean_object* v_nPrefix_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_namePrefix_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_val_1452_ = lean_ctor_get(v_nFields_x3f_1451_, 0);
v_nameComps_1453_ = l_Lean_Name_components(v_n_1450_);
v___x_1454_ = l_List_lengthTR___redArg(v_nameComps_1453_);
v_nPrefix_1455_ = lean_nat_sub(v___x_1454_, v_val_1452_);
lean_dec(v___x_1454_);
v___x_1456_ = lean_box(0);
v___x_1457_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1455_);
lean_inc(v_nameComps_1453_);
v___x_1458_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1453_, v_nameComps_1453_, v_nPrefix_1455_, v___x_1457_);
v_namePrefix_1459_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1456_, v___x_1458_);
v___x_1460_ = l_List_drop___redArg(v_nPrefix_1455_, v_nameComps_1453_);
lean_dec(v_nameComps_1453_);
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_namePrefix_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Name_components(v_n_1450_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1463_, lean_object* v_nFields_x3f_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1463_, v_nFields_x3f_1464_);
lean_dec(v_nFields_x3f_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_panic_fn_borrowed(v___x_1467_, v_msg_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
if (lean_obj_tag(v_a_1470_) == 0)
{
lean_object* v___x_1472_; 
lean_dec(v_info_1469_);
v___x_1472_ = l_List_reverse___redArg(v_a_1471_);
return v___x_1472_;
}
else
{
lean_object* v_head_1473_; lean_object* v_tail_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1489_; 
v_head_1473_ = lean_ctor_get(v_a_1470_, 0);
v_tail_1474_ = lean_ctor_get(v_a_1470_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_a_1470_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1476_ = v_a_1470_;
v_isShared_1477_ = v_isSharedCheck_1489_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_tail_1474_);
lean_inc(v_head_1473_);
lean_dec(v_a_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1489_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1478_ = 1;
lean_inc(v_head_1473_);
v___x_1479_ = l_Lean_Name_toString(v_head_1473_, v___x_1478_);
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_string_utf8_byte_size(v___x_1479_);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1479_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
v___x_1483_ = lean_box(0);
lean_inc(v_info_1469_);
v___x_1484_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1484_, 0, v_info_1469_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v_head_1473_);
lean_ctor_set(v___x_1484_, 3, v___x_1483_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v_a_1471_);
lean_ctor_set(v___x_1476_, 0, v___x_1484_);
v___x_1486_ = v___x_1476_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_a_1471_);
v___x_1486_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v_a_1470_ = v_tail_1474_;
v_a_1471_ = v___x_1486_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1491_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1492_ = lean_unsigned_to_nat(9u);
v___x_1493_ = lean_unsigned_to_nat(377u);
v___x_1494_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1495_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___x_1496_ = l_mkPanicMessageWithDecl(v___x_1495_, v___x_1494_, v___x_1493_, v___x_1492_, v___x_1491_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1497_, lean_object* v_nFields_x3f_1498_){
_start:
{
if (lean_obj_tag(v_stx_1497_) == 3)
{
lean_object* v_info_1499_; lean_object* v_rawVal_1500_; lean_object* v_val_1501_; lean_object* v_val_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_info_1499_ = lean_ctor_get(v_stx_1497_, 0);
lean_inc(v_info_1499_);
v_rawVal_1500_ = lean_ctor_get(v_stx_1497_, 1);
v_val_1501_ = lean_ctor_get(v_stx_1497_, 2);
v_val_1502_ = l_Lean_Name_eraseMacroScopes(v_val_1501_);
v___x_1503_ = l_Lean_Name_getNumParts(v_val_1502_);
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_dec_le(v___x_1503_, v___x_1504_);
lean_dec(v___x_1503_);
if (v___x_1505_ == 0)
{
if (lean_obj_tag(v_info_1499_) == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Syntax_identComponents_x3f(v_stx_1497_, v_nFields_x3f_1498_);
if (lean_obj_tag(v___x_1506_) == 1)
{
lean_object* v_val_1507_; lean_object* v_fst_1508_; 
lean_dec_ref_known(v_info_1499_, 4);
lean_dec(v_val_1502_);
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v_fst_1508_ = lean_ctor_get(v_val_1507_, 0);
lean_inc(v_fst_1508_);
lean_dec(v_val_1507_);
return v_fst_1508_;
}
else
{
lean_object* v_nameComps_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v___x_1506_);
v_nameComps_1509_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1502_, v_nFields_x3f_1498_);
v___x_1510_ = lean_box(0);
v___x_1511_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1499_, v_nameComps_1509_, v___x_1510_);
return v___x_1511_;
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref_known(v_stx_1497_, 4);
v___x_1512_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1502_, v_nFields_x3f_1498_);
v___x_1513_ = lean_box(0);
v___x_1514_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1499_, v___x_1512_, v___x_1513_);
return v___x_1514_;
}
}
else
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1523_; 
lean_inc_ref(v_rawVal_1500_);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_stx_1497_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1524_ = lean_ctor_get(v_stx_1497_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_stx_1497_, 2);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_stx_1497_, 1);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_stx_1497_, 0);
lean_dec(v_unused_1527_);
v___x_1516_ = v_stx_1497_;
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v_stx_1497_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 3, v___x_1518_);
lean_ctor_set(v___x_1516_, 2, v_val_1502_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_info_1499_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_rawVal_1500_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_val_1502_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1518_);
return v___x_1521_;
}
}
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_stx_1497_);
v___x_1528_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1529_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1528_);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1530_, lean_object* v_nFields_x3f_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Syntax_identComponents(v_stx_1530_, v_nFields_x3f_1531_);
lean_dec(v_nFields_x3f_1531_);
return v_res_1532_;
}
}
lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1533_, uint8_t v_firstChoiceOnly_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1535_, 0, v_stx_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*1, v_firstChoiceOnly_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Lean_Syntax_topDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1533_ = stack[0].m_obj;
uint8_t v_firstChoiceOnly_1534_ = stack[1].m_num;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_Syntax_topDown(v_stx_1533_, v_firstChoiceOnly_1534_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1537_, lean_object* v_firstChoiceOnly_1538_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1539_; lean_object* v_res_1540_; 
v_firstChoiceOnly_boxed_1539_ = lean_unbox(v_firstChoiceOnly_1538_);
v_res_1540_ = l_Lean_Syntax_topDown(v_stx_1537_, v_firstChoiceOnly_boxed_1539_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1541_, lean_object* v_____r_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_b_1543_);
v___x_1545_ = lean_apply_2(v_toPure_1541_, lean_box(0), v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1546_, lean_object* v_toPure_1547_, lean_object* v_____s_1548_){
_start:
{
lean_object* v_fst_1549_; 
v_fst_1549_ = lean_ctor_get(v_____s_1548_, 0);
if (lean_obj_tag(v_fst_1549_) == 0)
{
lean_object* v_snd_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v_toPure_1547_);
v_snd_1550_ = lean_ctor_get(v_____s_1548_, 1);
lean_inc(v_snd_1550_);
lean_dec_ref(v_____s_1548_);
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_apply_2(v___f_1546_, v___x_1551_, v_snd_1550_);
return v___x_1552_;
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1554_; 
lean_inc_ref(v_fst_1549_);
lean_dec_ref(v_____s_1548_);
lean_dec(v___f_1546_);
v_val_1553_ = lean_ctor_get(v_fst_1549_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v_fst_1549_, 1);
v___x_1554_ = lean_apply_2(v_toPure_1547_, lean_box(0), v_val_1553_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1555_, lean_object* v_toPure_1556_, lean_object* v___x_1557_, lean_object* v_____do__lift_1558_){
_start:
{
if (lean_obj_tag(v_____do__lift_1558_) == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_____do__lift_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_snd_1555_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
v___x_1562_ = lean_apply_2(v_toPure_1556_, lean_box(0), v___x_1561_);
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_snd_1555_);
v_a_1563_ = lean_ctor_get(v_____do__lift_1558_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_____do__lift_1558_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1565_ = v_____do__lift_1558_;
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v_____do__lift_1558_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1557_);
lean_ctor_set(v___x_1567_, 1, v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_apply_2(v_toPure_1556_, lean_box(0), v___x_1569_);
return v___x_1570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1573_, lean_object* v___x_1574_, lean_object* v_inst_1575_, lean_object* v_f_1576_, lean_object* v_firstChoiceOnly_1577_, lean_object* v_toBind_1578_, lean_object* v_a_1579_, lean_object* v_x_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1582_; lean_object* v_res_1583_; 
v_firstChoiceOnly_boxed_1582_ = lean_unbox(v_firstChoiceOnly_1577_);
v_res_1583_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1573_, v___x_1574_, v_inst_1575_, v_f_1576_, v_firstChoiceOnly_boxed_1582_, v_toBind_1578_, v_a_1579_, v_x_1580_, v___y_1581_);
return v_res_1583_;
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1587_, lean_object* v_stx_1588_, lean_object* v_inst_1589_, lean_object* v_f_1590_, uint8_t v_firstChoiceOnly_1591_, lean_object* v_toBind_1592_, lean_object* v___f_1593_, lean_object* v___x_1594_, lean_object* v___f_1595_, lean_object* v_____do__lift_1596_){
_start:
{
if (lean_obj_tag(v_____do__lift_1596_) == 0)
{
lean_object* v___x_1597_; 
lean_dec(v___f_1595_);
lean_dec(v___f_1593_);
lean_dec(v_toBind_1592_);
lean_dec(v_f_1590_);
lean_dec_ref(v_inst_1589_);
lean_dec(v_stx_1588_);
v___x_1597_ = lean_apply_2(v_toPure_1587_, lean_box(0), v_____do__lift_1596_);
return v___x_1597_;
}
else
{
if (lean_obj_tag(v_stx_1588_) == 1)
{
lean_object* v_a_1598_; lean_object* v_kind_1599_; lean_object* v_args_1600_; 
lean_dec(v___f_1595_);
v_a_1598_ = lean_ctor_get(v_____do__lift_1596_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v_____do__lift_1596_, 1);
v_kind_1599_ = lean_ctor_get(v_stx_1588_, 1);
lean_inc(v_kind_1599_);
v_args_1600_ = lean_ctor_get(v_stx_1588_, 2);
lean_inc_ref(v_args_1600_);
lean_dec_ref_known(v_stx_1588_, 3);
if (v_firstChoiceOnly_1591_ == 0)
{
lean_dec(v_kind_1599_);
goto v___jp_1601_;
}
else
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1611_ = lean_name_eq(v_kind_1599_, v___x_1610_);
lean_dec(v_kind_1599_);
if (v___x_1611_ == 0)
{
goto v___jp_1601_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec(v___f_1593_);
lean_dec(v_toBind_1592_);
lean_dec(v_toPure_1587_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_array_get(v___x_1594_, v_args_1600_, v___x_1612_);
lean_dec_ref(v_args_1600_);
v___x_1614_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1589_, v_f_1590_, v_firstChoiceOnly_1591_, v___x_1613_, v_a_1598_);
return v___x_1614_;
}
}
v___jp_1601_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = lean_box(v_firstChoiceOnly_1591_);
lean_inc(v_toBind_1592_);
lean_inc_ref(v_inst_1589_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1604_, 0, v_toPure_1587_);
lean_closure_set(v___f_1604_, 1, v___x_1602_);
lean_closure_set(v___f_1604_, 2, v_inst_1589_);
lean_closure_set(v___f_1604_, 3, v_f_1590_);
lean_closure_set(v___f_1604_, 4, v___x_1603_);
lean_closure_set(v___f_1604_, 5, v_toBind_1592_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1602_);
lean_ctor_set(v___x_1605_, 1, v_a_1598_);
v_sz_1606_ = lean_array_size(v_args_1600_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1589_, v_args_1600_, v___f_1604_, v_sz_1606_, v___x_1607_, v___x_1605_);
v___x_1609_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1608_, v___f_1593_);
return v___x_1609_;
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v___f_1593_);
lean_dec(v_toBind_1592_);
lean_dec(v_f_1590_);
lean_dec_ref(v_inst_1589_);
lean_dec(v_stx_1588_);
lean_dec(v_toPure_1587_);
v_a_1615_ = lean_ctor_get(v_____do__lift_1596_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v_____do__lift_1596_, 1);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_apply_2(v___f_1595_, v___x_1616_, v_a_1615_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1587_ = stack[0].m_obj;
lean_object* v_stx_1588_ = stack[1].m_obj;
lean_object* v_inst_1589_ = stack[2].m_obj;
lean_object* v_f_1590_ = stack[3].m_obj;
uint8_t v_firstChoiceOnly_1591_ = stack[4].m_num;
lean_object* v_toBind_1592_ = stack[5].m_obj;
lean_object* v___f_1593_ = stack[6].m_obj;
lean_object* v___x_1594_ = stack[7].m_obj;
lean_object* v___f_1595_ = stack[8].m_obj;
lean_object* v_____do__lift_1596_ = stack[9].m_obj;
lean_object* v_res_1618_;
v_res_1618_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1587_, v_stx_1588_, v_inst_1589_, v_f_1590_, v_firstChoiceOnly_1591_, v_toBind_1592_, v___f_1593_, v___x_1594_, v___f_1595_, v_____do__lift_1596_);
stack->m_obj
 = v_res_1618_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1619_, lean_object* v_stx_1620_, lean_object* v_inst_1621_, lean_object* v_f_1622_, lean_object* v_firstChoiceOnly_1623_, lean_object* v_toBind_1624_, lean_object* v___f_1625_, lean_object* v___x_1626_, lean_object* v___f_1627_, lean_object* v_____do__lift_1628_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1629_; lean_object* v_res_1630_; 
v_firstChoiceOnly_boxed_1629_ = lean_unbox(v_firstChoiceOnly_1623_);
v_res_1630_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1619_, v_stx_1620_, v_inst_1621_, v_f_1622_, v_firstChoiceOnly_boxed_1629_, v_toBind_1624_, v___f_1625_, v___x_1626_, v___f_1627_, v_____do__lift_1628_);
lean_dec(v___x_1626_);
return v_res_1630_;
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1631_, lean_object* v_f_1632_, uint8_t v_firstChoiceOnly_1633_, lean_object* v_stx_1634_, lean_object* v_b_1635_){
_start:
{
lean_object* v_toApplicative_1636_; lean_object* v_toBind_1637_; lean_object* v_toPure_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___f_1644_; lean_object* v___x_1645_; 
v_toApplicative_1636_ = lean_ctor_get(v_inst_1631_, 0);
v_toBind_1637_ = lean_ctor_get(v_inst_1631_, 1);
lean_inc_n(v_toBind_1637_, 2);
v_toPure_1638_ = lean_ctor_get(v_toApplicative_1636_, 1);
lean_inc_n(v_toPure_1638_, 3);
v___x_1639_ = lean_box(0);
lean_inc(v_f_1632_);
lean_inc(v_stx_1634_);
v___x_1640_ = lean_apply_2(v_f_1632_, v_stx_1634_, v_b_1635_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1641_, 0, v_toPure_1638_);
lean_inc_ref(v___f_1641_);
v___f_1642_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1642_, 0, v___f_1641_);
lean_closure_set(v___f_1642_, 1, v_toPure_1638_);
v___x_1643_ = lean_box(v_firstChoiceOnly_1633_);
v___f_1644_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1644_, 0, v_toPure_1638_);
lean_closure_set(v___f_1644_, 1, v_stx_1634_);
lean_closure_set(v___f_1644_, 2, v_inst_1631_);
lean_closure_set(v___f_1644_, 3, v_f_1632_);
lean_closure_set(v___f_1644_, 4, v___x_1643_);
lean_closure_set(v___f_1644_, 5, v_toBind_1637_);
lean_closure_set(v___f_1644_, 6, v___f_1642_);
lean_closure_set(v___f_1644_, 7, v___x_1639_);
lean_closure_set(v___f_1644_, 8, v___f_1641_);
v___x_1645_ = lean_apply_4(v_toBind_1637_, lean_box(0), lean_box(0), v___x_1640_, v___f_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1631_ = stack[0].m_obj;
lean_object* v_f_1632_ = stack[1].m_obj;
uint8_t v_firstChoiceOnly_1633_ = stack[2].m_num;
lean_object* v_stx_1634_ = stack[3].m_obj;
lean_object* v_b_1635_ = stack[4].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1631_, v_f_1632_, v_firstChoiceOnly_1633_, v_stx_1634_, v_b_1635_);
stack->m_obj
 = v_res_1646_;
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1647_, lean_object* v___x_1648_, lean_object* v_inst_1649_, lean_object* v_f_1650_, uint8_t v_firstChoiceOnly_1651_, lean_object* v_toBind_1652_, lean_object* v_a_1653_, lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_snd_1656_; lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_snd_1656_ = lean_ctor_get(v___y_1655_, 1);
lean_inc_n(v_snd_1656_, 2);
lean_dec_ref(v___y_1655_);
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1657_, 0, v_snd_1656_);
lean_closure_set(v___f_1657_, 1, v_toPure_1647_);
lean_closure_set(v___f_1657_, 2, v___x_1648_);
v___x_1658_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1649_, v_f_1650_, v_firstChoiceOnly_1651_, v_a_1653_, v_snd_1656_);
v___x_1659_ = lean_apply_4(v_toBind_1652_, lean_box(0), lean_box(0), v___x_1658_, v___f_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1647_ = stack[0].m_obj;
lean_object* v___x_1648_ = stack[1].m_obj;
lean_object* v_inst_1649_ = stack[2].m_obj;
lean_object* v_f_1650_ = stack[3].m_obj;
uint8_t v_firstChoiceOnly_1651_ = stack[4].m_num;
lean_object* v_toBind_1652_ = stack[5].m_obj;
lean_object* v_a_1653_ = stack[6].m_obj;
lean_object* v___y_1655_ = stack[8].m_obj;
lean_object* v_res_1660_;
v_res_1660_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1647_, v___x_1648_, v_inst_1649_, v_f_1650_, v_firstChoiceOnly_1651_, v_toBind_1652_, v_a_1653_, lean_box(0), v___y_1655_);
stack->m_obj
 = v_res_1660_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1661_, lean_object* v_f_1662_, lean_object* v_firstChoiceOnly_1663_, lean_object* v_stx_1664_, lean_object* v_b_1665_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1666_; lean_object* v_res_1667_; 
v_firstChoiceOnly_boxed_1666_ = lean_unbox(v_firstChoiceOnly_1663_);
v_res_1667_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1661_, v_f_1662_, v_firstChoiceOnly_boxed_1666_, v_stx_1664_, v_b_1665_);
return v_res_1667_;
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1668_, lean_object* v_inst_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_f_1671_, uint8_t v_firstChoiceOnly_1672_, lean_object* v_stx_1673_, lean_object* v_b_1674_, lean_object* v_inst_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1669_, v_f_1671_, v_firstChoiceOnly_1672_, v_stx_1673_, v_b_1674_);
return v___x_1676_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1669_ = stack[1].m_obj;
lean_object* v_f_1671_ = stack[3].m_obj;
uint8_t v_firstChoiceOnly_1672_ = stack[4].m_num;
lean_object* v_stx_1673_ = stack[5].m_obj;
lean_object* v_b_1674_ = stack[6].m_obj;
lean_object* v_inst_1675_ = stack[7].m_obj;
lean_object* v_res_1677_;
v_res_1677_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_box(0), v_inst_1669_, lean_box(0), v_f_1671_, v_firstChoiceOnly_1672_, v_stx_1673_, v_b_1674_, v_inst_1675_);
stack->m_obj
 = v_res_1677_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1678_, lean_object* v_inst_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_f_1681_, lean_object* v_firstChoiceOnly_1682_, lean_object* v_stx_1683_, lean_object* v_b_1684_, lean_object* v_inst_1685_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1686_; lean_object* v_res_1687_; 
v_firstChoiceOnly_boxed_1686_ = lean_unbox(v_firstChoiceOnly_1682_);
v_res_1687_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1678_, v_inst_1679_, v_00_u03b2_1680_, v_f_1681_, v_firstChoiceOnly_boxed_1686_, v_stx_1683_, v_b_1684_, v_inst_1685_);
lean_dec(v_inst_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1688_, lean_object* v_____do__lift_1689_){
_start:
{
lean_object* v_a_1690_; lean_object* v___x_1691_; 
v_a_1690_ = lean_ctor_get(v_____do__lift_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v_____do__lift_1689_);
v___x_1691_ = lean_apply_2(v_toPure_1688_, lean_box(0), v_a_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1692_, lean_object* v_toBind_1693_, lean_object* v___f_1694_, lean_object* v_00_u03b2_1695_, lean_object* v_x_1696_, lean_object* v_init_1697_, lean_object* v_f_1698_){
_start:
{
uint8_t v_firstChoiceOnly_1699_; lean_object* v_stx_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_firstChoiceOnly_1699_ = lean_ctor_get_uint8(v_x_1696_, sizeof(void*)*1);
v_stx_1700_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_stx_1700_);
lean_dec_ref(v_x_1696_);
v___x_1701_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1692_, v_f_1698_, v_firstChoiceOnly_1699_, v_stx_1700_, v_init_1697_);
v___x_1702_ = lean_apply_4(v_toBind_1693_, lean_box(0), lean_box(0), v___x_1701_, v___f_1694_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1703_){
_start:
{
lean_object* v_toApplicative_1704_; lean_object* v_toBind_1705_; lean_object* v_toPure_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; 
v_toApplicative_1704_ = lean_ctor_get(v_inst_1703_, 0);
v_toBind_1705_ = lean_ctor_get(v_inst_1703_, 1);
lean_inc(v_toBind_1705_);
v_toPure_1706_ = lean_ctor_get(v_toApplicative_1704_, 1);
lean_inc(v_toPure_1706_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1707_, 0, v_toPure_1706_);
v___f_1708_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1708_, 0, v_inst_1703_);
lean_closure_set(v___f_1708_, 1, v_toBind_1705_);
lean_closure_set(v___f_1708_, 2, v___f_1707_);
return v___f_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1709_, lean_object* v_inst_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1713_, lean_object* v_val_1714_){
_start:
{
if (lean_obj_tag(v_info_1713_) == 0)
{
lean_object* v_leading_1715_; lean_object* v_trailing_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_leading_1715_ = lean_ctor_get(v_info_1713_, 0);
lean_inc_ref(v_leading_1715_);
v_trailing_1716_ = lean_ctor_get(v_info_1713_, 2);
lean_inc_ref(v_trailing_1716_);
lean_dec_ref_known(v_info_1713_, 4);
v___x_1717_ = lean_substring_tostring(v_leading_1715_);
v___x_1718_ = lean_string_append(v___x_1717_, v_val_1714_);
v___x_1719_ = lean_substring_tostring(v_trailing_1716_);
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
lean_dec_ref(v___x_1719_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_info_1713_);
v___x_1721_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1722_ = lean_string_append(v___x_1721_, v_val_1714_);
v___x_1723_ = lean_string_append(v___x_1722_, v___x_1721_);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1724_, lean_object* v_val_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1724_, v_val_1725_);
lean_dec_ref(v_val_1725_);
return v_res_1726_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1727_, lean_object* v_as_1728_, size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_b_1731_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_b_1731_);
return v___x_1733_;
}
else
{
lean_object* v_snd_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1761_; 
v_snd_1734_ = lean_ctor_get(v_b_1731_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_b_1731_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_b_1731_, 0);
lean_dec(v_unused_1762_);
v___x_1736_ = v_b_1731_;
v_isShared_1737_ = v_isSharedCheck_1761_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snd_1734_);
lean_dec(v_b_1731_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1761_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_a_1738_; lean_object* v___x_1739_; 
v_a_1738_ = lean_array_uget_borrowed(v_as_1728_, v_i_1730_);
lean_inc(v_snd_1734_);
lean_inc(v_a_1738_);
v___x_1739_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1727_, v_a_1738_, v_snd_1734_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; 
lean_del_object(v___x_1736_);
lean_dec(v_snd_1734_);
v___x_1740_ = lean_box(0);
return v___x_1740_;
}
else
{
lean_object* v_val_1741_; 
v_val_1741_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_val_1741_);
if (lean_obj_tag(v_val_1741_) == 0)
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1751_; 
v_isSharedCheck_1751_ = !lean_is_exclusive(v_val_1741_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v_val_1741_, 0);
lean_dec(v_unused_1752_);
v___x_1743_ = v_val_1741_;
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v_val_1741_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1739_);
v___x_1746_ = v___x_1736_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_snd_1734_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 1);
lean_ctor_set(v___x_1743_, 0, v___x_1746_);
v___x_1748_ = v___x_1743_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec_ref_known(v___x_1739_, 1);
lean_dec(v_snd_1734_);
v_a_1753_ = lean_ctor_get(v_val_1741_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v_val_1741_, 1);
v___x_1754_ = lean_box(0);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v_a_1753_);
lean_ctor_set(v___x_1736_, 0, v___x_1754_);
v___x_1756_ = v___x_1736_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_a_1753_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
size_t v___x_1757_; size_t v___x_1758_; 
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1730_, v___x_1757_);
v_i_1730_ = v___x_1758_;
v_b_1731_ = v___x_1756_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_firstChoiceOnly_1727_ = stack[0].m_num;
lean_object* v_as_1728_ = stack[1].m_obj;
size_t v_sz_1729_ = stack[2].m_num;
size_t v_i_1730_ = stack[3].m_num;
lean_object* v_b_1731_ = stack[4].m_obj;
lean_object* v_res_1763_;
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1727_, v_as_1728_, v_sz_1729_, v_i_1730_, v_b_1731_);
stack->m_obj
 = v_res_1763_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1764_, lean_object* v_a_1765_, lean_object* v_b_1766_){
_start:
{
lean_object* v_array_1767_; lean_object* v_start_1768_; lean_object* v_stop_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1788_; 
v_array_1767_ = lean_ctor_get(v_a_1765_, 0);
v_start_1768_ = lean_ctor_get(v_a_1765_, 1);
v_stop_1769_ = lean_ctor_get(v_a_1765_, 2);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_a_1765_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1771_ = v_a_1765_;
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_stop_1769_);
lean_inc(v_start_1768_);
lean_inc(v_array_1767_);
lean_dec(v_a_1765_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_nat_dec_lt(v_start_1768_, v_stop_1769_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_del_object(v___x_1771_);
lean_dec(v_stop_1769_);
lean_dec(v_start_1768_);
lean_dec_ref(v_array_1767_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_b_1766_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_array_fget_borrowed(v_array_1767_, v_start_1768_);
lean_inc(v___x_1775_);
v___x_1776_ = l_Lean_Syntax_reprint(v___x_1775_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1777_; 
lean_del_object(v___x_1771_);
lean_dec(v_stop_1769_);
lean_dec(v_start_1768_);
lean_dec_ref(v_array_1767_);
v___x_1777_ = lean_box(0);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; uint8_t v___x_1779_; 
v_val_1778_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1779_ = lean_string_dec_eq(v_val_1764_, v_val_1778_);
lean_dec(v_val_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; 
lean_del_object(v___x_1771_);
lean_dec(v_stop_1769_);
lean_dec(v_start_1768_);
lean_dec_ref(v_array_1767_);
v___x_1780_ = lean_box(0);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_start_1768_, v___x_1782_);
lean_dec(v_start_1768_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 1, v___x_1783_);
v___x_1785_ = v___x_1771_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_array_1767_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_stop_1769_);
v___x_1785_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v_a_1765_ = v___x_1785_;
v_b_1766_ = v___x_1781_;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1789_, lean_object* v_stx_1790_, lean_object* v_b_1791_){
_start:
{
lean_object* v_b_1793_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___x_1807_; lean_object* v_a_1809_; 
v___x_1807_ = lean_box(0);
switch(lean_obj_tag(v_stx_1790_))
{
case 2:
{
lean_object* v_info_1818_; lean_object* v_val_1819_; lean_object* v___x_1820_; lean_object* v_s_1821_; 
v_info_1818_ = lean_ctor_get(v_stx_1790_, 0);
v_val_1819_ = lean_ctor_get(v_stx_1790_, 1);
lean_inc(v_info_1818_);
v___x_1820_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1818_, v_val_1819_);
v_s_1821_ = lean_string_append(v_b_1791_, v___x_1820_);
lean_dec_ref(v___x_1820_);
v_a_1809_ = v_s_1821_;
goto v___jp_1808_;
}
case 3:
{
lean_object* v_rawVal_1822_; lean_object* v_info_1823_; lean_object* v_str_1824_; lean_object* v_startPos_1825_; lean_object* v_stopPos_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_s_1829_; 
v_rawVal_1822_ = lean_ctor_get(v_stx_1790_, 1);
v_info_1823_ = lean_ctor_get(v_stx_1790_, 0);
v_str_1824_ = lean_ctor_get(v_rawVal_1822_, 0);
v_startPos_1825_ = lean_ctor_get(v_rawVal_1822_, 1);
v_stopPos_1826_ = lean_ctor_get(v_rawVal_1822_, 2);
v___x_1827_ = lean_string_utf8_extract(v_str_1824_, v_startPos_1825_, v_stopPos_1826_);
lean_inc(v_info_1823_);
v___x_1828_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1823_, v___x_1827_);
lean_dec_ref(v___x_1827_);
v_s_1829_ = lean_string_append(v_b_1791_, v___x_1828_);
lean_dec_ref(v___x_1828_);
v_a_1809_ = v_s_1829_;
goto v___jp_1808_;
}
case 1:
{
lean_object* v_kind_1830_; lean_object* v_args_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_kind_1830_ = lean_ctor_get(v_stx_1790_, 1);
v_args_1831_ = lean_ctor_get(v_stx_1790_, 2);
v___x_1832_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1833_ = lean_name_eq(v_kind_1830_, v___x_1832_);
if (v___x_1833_ == 0)
{
v_a_1809_ = v_b_1791_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_array_get_borrowed(v___x_1807_, v_args_1831_, v___x_1834_);
lean_inc(v___x_1835_);
v___x_1836_ = l_Lean_Syntax_reprint(v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref_known(v_stx_1790_, 3);
lean_dec_ref(v_b_1791_);
v___x_1837_ = lean_box(0);
return v___x_1837_;
}
else
{
lean_object* v_val_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_val_1838_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_array_get_size(v_args_1831_);
lean_inc_ref(v_args_1831_);
v___x_1841_ = l_Array_toSubarray___redArg(v_args_1831_, v___x_1839_, v___x_1840_);
v___x_1842_ = lean_box(0);
v___x_1843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1838_, v___x_1841_, v___x_1842_);
lean_dec(v_val_1838_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref_known(v_stx_1790_, 3);
lean_dec_ref(v_b_1791_);
v___x_1844_ = lean_box(0);
return v___x_1844_;
}
else
{
lean_dec_ref_known(v___x_1843_, 1);
v_a_1809_ = v_b_1791_;
goto v___jp_1808_;
}
}
}
}
default: 
{
v_a_1809_ = v_b_1791_;
goto v___jp_1808_;
}
}
v___jp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_b_1793_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
v___jp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___y_1798_);
v_sz_1801_ = lean_array_size(v___y_1797_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1789_, v___y_1797_, v_sz_1801_, v___x_1802_, v___x_1800_);
lean_dec_ref(v___y_1797_);
if (lean_obj_tag(v___x_1803_) == 0)
{
return v___x_1799_;
}
else
{
lean_object* v_val_1804_; lean_object* v_fst_1805_; 
v_val_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_val_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v_fst_1805_ = lean_ctor_get(v_val_1804_, 0);
if (lean_obj_tag(v_fst_1805_) == 0)
{
lean_object* v_snd_1806_; 
v_snd_1806_ = lean_ctor_get(v_val_1804_, 1);
lean_inc(v_snd_1806_);
lean_dec(v_val_1804_);
v_b_1793_ = v_snd_1806_;
goto v___jp_1792_;
}
else
{
lean_inc_ref(v_fst_1805_);
lean_dec(v_val_1804_);
return v_fst_1805_;
}
}
}
v___jp_1808_:
{
if (lean_obj_tag(v_stx_1790_) == 1)
{
if (v_firstChoiceOnly_1789_ == 0)
{
lean_object* v_args_1810_; 
v_args_1810_ = lean_ctor_get(v_stx_1790_, 2);
lean_inc_ref(v_args_1810_);
lean_dec_ref_known(v_stx_1790_, 3);
v___y_1797_ = v_args_1810_;
v___y_1798_ = v_a_1809_;
goto v___jp_1796_;
}
else
{
lean_object* v_kind_1811_; lean_object* v_args_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_kind_1811_ = lean_ctor_get(v_stx_1790_, 1);
lean_inc(v_kind_1811_);
v_args_1812_ = lean_ctor_get(v_stx_1790_, 2);
lean_inc_ref(v_args_1812_);
lean_dec_ref_known(v_stx_1790_, 3);
v___x_1813_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1814_ = lean_name_eq(v_kind_1811_, v___x_1813_);
lean_dec(v_kind_1811_);
if (v___x_1814_ == 0)
{
v___y_1797_ = v_args_1812_;
v___y_1798_ = v_a_1809_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get(v___x_1807_, v_args_1812_, v___x_1815_);
lean_dec_ref(v_args_1812_);
v_stx_1790_ = v___x_1816_;
v_b_1791_ = v_a_1809_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1790_);
v_b_1793_ = v_a_1809_;
goto v___jp_1792_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_firstChoiceOnly_1789_ = stack[0].m_num;
lean_object* v_stx_1790_ = stack[1].m_obj;
lean_object* v_b_1791_ = stack[2].m_obj;
lean_object* v_res_1845_;
v_res_1845_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1789_, v_stx_1790_, v_b_1791_);
stack->m_obj
 = v_res_1845_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1846_){
_start:
{
lean_object* v_s_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v_s_1847_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1848_ = 1;
v___x_1849_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1848_, v_stx_1846_, v_s_1847_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_val_1851_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v___x_1849_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_val_1851_);
lean_dec(v___x_1849_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_a_1855_; lean_object* v___x_1857_; 
v_a_1855_ = lean_ctor_get(v_val_1851_, 0);
lean_inc(v_a_1855_);
lean_dec(v_val_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_a_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1860_, lean_object* v_a_1861_, lean_object* v_b_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1860_, v_a_1861_, v_b_1862_);
lean_dec_ref(v_val_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1864_, lean_object* v_as_1865_, lean_object* v_sz_1866_, lean_object* v_i_1867_, lean_object* v_b_1868_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1869_; size_t v_sz_boxed_1870_; size_t v_i_boxed_1871_; lean_object* v_res_1872_; 
v_firstChoiceOnly_boxed_1869_ = lean_unbox(v_firstChoiceOnly_1864_);
v_sz_boxed_1870_ = lean_unbox_usize(v_sz_1866_);
lean_dec(v_sz_1866_);
v_i_boxed_1871_ = lean_unbox_usize(v_i_1867_);
lean_dec(v_i_1867_);
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1869_, v_as_1865_, v_sz_boxed_1870_, v_i_boxed_1871_, v_b_1868_);
lean_dec_ref(v_as_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1873_, lean_object* v_stx_1874_, lean_object* v_b_1875_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1876_; lean_object* v_res_1877_; 
v_firstChoiceOnly_boxed_1876_ = lean_unbox(v_firstChoiceOnly_1873_);
v_res_1877_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1876_, v_stx_1874_, v_b_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1878_, lean_object* v_inst_1879_, lean_object* v_R_1880_, lean_object* v_a_1881_, lean_object* v_b_1882_, lean_object* v_c_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1878_, v_a_1881_, v_b_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1885_, lean_object* v_inst_1886_, lean_object* v_R_1887_, lean_object* v_a_1888_, lean_object* v_b_1889_, lean_object* v_c_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1885_, v_inst_1886_, v_R_1887_, v_a_1888_, v_b_1889_, v_c_1890_);
lean_dec_ref(v_val_1885_);
return v_res_1891_;
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1900_, lean_object* v_stx_1901_){
_start:
{
lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = l_Lean_Syntax_isMissing(v_stx_1901_);
if (v___x_1903_ == 0)
{
if (lean_obj_tag(v_stx_1901_) == 1)
{
lean_object* v_kind_1904_; lean_object* v_args_1905_; 
v_kind_1904_ = lean_ctor_get(v_stx_1901_, 1);
v_args_1905_ = lean_ctor_get(v_stx_1901_, 2);
if (v_firstChoiceOnly_1900_ == 0)
{
goto v___jp_1906_;
}
else
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1916_ = lean_name_eq(v_kind_1904_, v___x_1915_);
if (v___x_1916_ == 0)
{
goto v___jp_1906_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = lean_array_get_borrowed(v___x_1917_, v_args_1905_, v___x_1918_);
v_stx_1901_ = v___x_1919_;
goto _start;
}
}
v___jp_1906_:
{
lean_object* v___x_1907_; size_t v_sz_1908_; size_t v___x_1909_; lean_object* v___x_1910_; lean_object* v_fst_1911_; 
v___x_1907_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1908_ = lean_array_size(v_args_1905_);
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1900_, v_args_1905_, v_sz_1908_, v___x_1909_, v___x_1907_);
v_fst_1911_ = lean_ctor_get(v___x_1910_, 0);
if (lean_obj_tag(v_fst_1911_) == 0)
{
lean_object* v_snd_1912_; lean_object* v___x_1913_; 
v_snd_1912_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_snd_1912_);
lean_dec_ref(v___x_1910_);
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_snd_1912_);
return v___x_1913_;
}
else
{
lean_object* v_val_1914_; 
lean_inc_ref(v_fst_1911_);
lean_dec_ref(v___x_1910_);
v_val_1914_ = lean_ctor_get(v_fst_1911_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_fst_1911_, 1);
return v_val_1914_;
}
}
}
else
{
lean_object* v___x_1921_; 
v___x_1921_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1921_;
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = lean_box(v___x_1903_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1902_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_firstChoiceOnly_1900_ = stack[0].m_num;
lean_object* v_stx_1901_ = stack[1].m_obj;
lean_object* v_res_1926_;
v_res_1926_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1900_, v_stx_1901_);
stack->m_obj
 = v_res_1926_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1927_, lean_object* v_as_1928_, size_t v_sz_1929_, size_t v_i_1930_, lean_object* v_b_1931_){
_start:
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_usize_dec_lt(v_i_1930_, v_sz_1929_);
if (v___x_1932_ == 0)
{
return v_b_1931_;
}
else
{
lean_object* v_snd_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1951_; 
v_snd_1933_ = lean_ctor_get(v_b_1931_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_b_1931_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_b_1931_, 0);
lean_dec(v_unused_1952_);
v___x_1935_ = v_b_1931_;
v_isShared_1936_ = v_isSharedCheck_1951_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_snd_1933_);
lean_dec(v_b_1931_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1951_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_array_uget_borrowed(v_as_1928_, v_i_1930_);
v___x_1938_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1927_, v_a_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1939_);
v___x_1941_ = v___x_1935_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_snd_1933_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_dec(v_snd_1933_);
v_a_1943_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1944_ = lean_box(0);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_a_1943_);
lean_ctor_set(v___x_1935_, 0, v___x_1944_);
v___x_1946_ = v___x_1935_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_a_1943_);
v___x_1946_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
size_t v___x_1947_; size_t v___x_1948_; 
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_add(v_i_1930_, v___x_1947_);
v_i_1930_ = v___x_1948_;
v_b_1931_ = v___x_1946_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_firstChoiceOnly_1927_ = stack[0].m_num;
lean_object* v_as_1928_ = stack[1].m_obj;
size_t v_sz_1929_ = stack[2].m_num;
size_t v_i_1930_ = stack[3].m_num;
lean_object* v_b_1931_ = stack[4].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1927_, v_as_1928_, v_sz_1929_, v_i_1930_, v_b_1931_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1954_, lean_object* v_as_1955_, lean_object* v_sz_1956_, lean_object* v_i_1957_, lean_object* v_b_1958_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1959_; size_t v_sz_boxed_1960_; size_t v_i_boxed_1961_; lean_object* v_res_1962_; 
v_firstChoiceOnly_boxed_1959_ = lean_unbox(v_firstChoiceOnly_1954_);
v_sz_boxed_1960_ = lean_unbox_usize(v_sz_1956_);
lean_dec(v_sz_1956_);
v_i_boxed_1961_ = lean_unbox_usize(v_i_1957_);
lean_dec(v_i_1957_);
v_res_1962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1959_, v_as_1955_, v_sz_boxed_1960_, v_i_boxed_1961_, v_b_1958_);
lean_dec_ref(v_as_1955_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1963_, lean_object* v_stx_1964_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1965_; lean_object* v_res_1966_; 
v_firstChoiceOnly_boxed_1965_ = lean_unbox(v_firstChoiceOnly_1963_);
v_res_1966_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1965_, v_stx_1964_);
lean_dec(v_stx_1964_);
return v_res_1966_;
}
}
uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1967_){
_start:
{
uint8_t v___x_1968_; lean_object* v___y_1970_; lean_object* v___x_1974_; lean_object* v_a_1975_; 
v___x_1968_ = 0;
v___x_1974_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1968_, v_stx_1967_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
v___y_1970_ = v_a_1975_;
goto v___jp_1969_;
v___jp_1969_:
{
lean_object* v_fst_1971_; 
v_fst_1971_ = lean_ctor_get(v___y_1970_, 0);
lean_inc(v_fst_1971_);
lean_dec_ref(v___y_1970_);
if (lean_obj_tag(v_fst_1971_) == 0)
{
return v___x_1968_;
}
else
{
lean_object* v_val_1972_; uint8_t v___x_1973_; 
v_val_1972_ = lean_ctor_get(v_fst_1971_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v_fst_1971_, 1);
v___x_1973_ = lean_unbox(v_val_1972_);
lean_dec(v_val_1972_);
return v___x_1973_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_hasMissing_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1967_ = stack[0].m_obj;
uint8_t v_res_1976_;
v_res_1976_ = l_Lean_Syntax_hasMissing(v_stx_1967_);
stack->m_num = v_res_1976_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1977_){
_start:
{
uint8_t v_res_1978_; lean_object* v_r_1979_; 
v_res_1978_ = l_Lean_Syntax_hasMissing(v_stx_1977_);
lean_dec(v_stx_1977_);
v_r_1979_ = lean_box(v_res_1978_);
return v_r_1979_;
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1980_, lean_object* v_stx_1981_, lean_object* v_b_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1980_, v_stx_1981_);
return v___x_1983_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_firstChoiceOnly_1980_ = stack[0].m_num;
lean_object* v_stx_1981_ = stack[1].m_obj;
lean_object* v_b_1982_ = stack[2].m_obj;
lean_object* v_res_1984_;
v_res_1984_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_1980_, v_stx_1981_, v_b_1982_);
stack->m_obj
 = v_res_1984_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1985_, lean_object* v_stx_1986_, lean_object* v_b_1987_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1988_; lean_object* v_res_1989_; 
v_firstChoiceOnly_boxed_1988_ = lean_unbox(v_firstChoiceOnly_1985_);
v_res_1989_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1988_, v_stx_1986_, v_b_1987_);
lean_dec_ref(v_b_1987_);
lean_dec(v_stx_1986_);
return v_res_1989_;
}
}
lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1990_, uint8_t v_canonicalOnly_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Syntax_getPos_x3f(v_stx_1990_, v_canonicalOnly_1991_);
if (lean_obj_tag(v___x_1992_) == 1)
{
lean_object* v_val_1993_; lean_object* v___x_1994_; 
v_val_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1990_, v_canonicalOnly_1991_);
if (lean_obj_tag(v___x_1994_) == 1)
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_val_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_val_1993_);
lean_ctor_set(v___x_1999_, 1, v_val_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v___x_1994_);
lean_dec(v_val_1993_);
v___x_2004_ = lean_box(0);
return v___x_2004_;
}
}
else
{
lean_object* v___x_2005_; 
lean_dec(v___x_1992_);
v___x_2005_ = lean_box(0);
return v___x_2005_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_getRange_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1990_ = stack[0].m_obj;
uint8_t v_canonicalOnly_1991_ = stack[1].m_num;
lean_object* v_res_2006_;
v_res_2006_ = l_Lean_Syntax_getRange_x3f(v_stx_1990_, v_canonicalOnly_1991_);
stack->m_obj
 = v_res_2006_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_2007_, lean_object* v_canonicalOnly_2008_){
_start:
{
uint8_t v_canonicalOnly_boxed_2009_; lean_object* v_res_2010_; 
v_canonicalOnly_boxed_2009_ = lean_unbox(v_canonicalOnly_2008_);
v_res_2010_ = l_Lean_Syntax_getRange_x3f(v_stx_2007_, v_canonicalOnly_boxed_2009_);
lean_dec(v_stx_2007_);
return v_res_2010_;
}
}
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_2011_, uint8_t v_canonicalOnly_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Syntax_getPos_x3f(v_stx_2011_, v_canonicalOnly_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2016_; 
v_val_2015_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_val_2015_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2016_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_2011_, v_canonicalOnly_2012_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
lean_dec(v_val_2015_);
v___x_2017_ = lean_box(0);
return v___x_2017_;
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_val_2018_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_val_2015_);
lean_ctor_set(v___x_2022_, 1, v_val_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_getRangeWithTrailing_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2011_ = stack[0].m_obj;
uint8_t v_canonicalOnly_2012_ = stack[1].m_num;
lean_object* v_res_2027_;
v_res_2027_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_2011_, v_canonicalOnly_2012_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_2028_, lean_object* v_canonicalOnly_2029_){
_start:
{
uint8_t v_canonicalOnly_boxed_2030_; lean_object* v_res_2031_; 
v_canonicalOnly_boxed_2030_ = lean_unbox(v_canonicalOnly_2029_);
v_res_2031_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_2028_, v_canonicalOnly_boxed_2030_);
lean_dec(v_stx_2028_);
return v_res_2031_;
}
}
lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_2032_, uint8_t v_canonical_2033_){
_start:
{
lean_object* v_start_2034_; lean_object* v_stop_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2044_; 
v_start_2034_ = lean_ctor_get(v_range_2032_, 0);
v_stop_2035_ = lean_ctor_get(v_range_2032_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_range_2032_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2037_ = v_range_2032_;
v_isShared_2038_ = v_isSharedCheck_2044_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_stop_2035_);
lean_inc(v_start_2034_);
lean_dec(v_range_2032_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2044_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2039_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2039_, 0, v_start_2034_);
lean_ctor_set(v___x_2039_, 1, v_stop_2035_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*2, v_canonical_2033_);
v___x_2040_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 2);
lean_ctor_set(v___x_2037_, 1, v___x_2040_);
lean_ctor_set(v___x_2037_, 0, v___x_2039_);
v___x_2042_ = v___x_2037_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_ofRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_2032_ = stack[0].m_obj;
uint8_t v_canonical_2033_ = stack[1].m_num;
lean_object* v_res_2045_;
v_res_2045_ = l_Lean_Syntax_ofRange(v_range_2032_, v_canonical_2033_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2046_, lean_object* v_canonical_2047_){
_start:
{
uint8_t v_canonical_boxed_2048_; lean_object* v_res_2049_; 
v_canonical_boxed_2048_ = lean_unbox(v_canonical_2047_);
v_res_2049_ = l_Lean_Syntax_ofRange(v_range_2046_, v_canonical_boxed_2048_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2054_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2054_, 0, v_stx_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_ctor_set(v___x_2054_, 2, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2055_, lean_object* v_stx_2056_){
_start:
{
lean_object* v_parents_2057_; lean_object* v_idxs_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_parents_2057_ = lean_ctor_get(v_t_2055_, 1);
v_idxs_2058_ = lean_ctor_get(v_t_2055_, 2);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_t_2055_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v_t_2055_, 0);
lean_dec(v_unused_2066_);
v___x_2060_ = v_t_2055_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_idxs_2058_);
lean_inc(v_parents_2057_);
lean_dec(v_t_2055_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v_stx_2056_);
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_stx_2056_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_parents_2057_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_idxs_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2067_, lean_object* v_idx_2068_){
_start:
{
lean_object* v_cur_2069_; lean_object* v_parents_2070_; lean_object* v_idxs_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2091_; 
v_cur_2069_ = lean_ctor_get(v_t_2067_, 0);
v_parents_2070_ = lean_ctor_get(v_t_2067_, 1);
v_idxs_2071_ = lean_ctor_get(v_t_2067_, 2);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_t_2067_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2073_ = v_t_2067_;
v_isShared_2074_ = v_isSharedCheck_2091_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_idxs_2071_);
lean_inc(v_parents_2070_);
lean_inc(v_cur_2069_);
lean_dec(v_t_2067_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2091_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = l_Lean_Syntax_getNumArgs(v_cur_2069_);
v___x_2076_ = lean_nat_dec_lt(v_idx_2068_, v___x_2075_);
lean_dec(v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_array_push(v_parents_2070_, v_cur_2069_);
v___x_2079_ = lean_array_push(v_idxs_2071_, v_idx_2068_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 2, v___x_2079_);
lean_ctor_set(v___x_2073_, 1, v___x_2078_);
lean_ctor_set(v___x_2073_, 0, v___x_2077_);
v___x_2081_ = v___x_2073_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2083_ = l_Lean_Syntax_getArg(v_cur_2069_, v_idx_2068_);
v___x_2084_ = lean_box(0);
v___x_2085_ = l_Lean_Syntax_setArg(v_cur_2069_, v_idx_2068_, v___x_2084_);
v___x_2086_ = lean_array_push(v_parents_2070_, v___x_2085_);
v___x_2087_ = lean_array_push(v_idxs_2071_, v_idx_2068_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 2, v___x_2087_);
lean_ctor_set(v___x_2073_, 1, v___x_2086_);
lean_ctor_set(v___x_2073_, 0, v___x_2083_);
v___x_2089_ = v___x_2073_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2092_){
_start:
{
lean_object* v_cur_2093_; lean_object* v_parents_2094_; lean_object* v_idxs_2095_; lean_object* v___y_2097_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_cur_2093_ = lean_ctor_get(v_t_2092_, 0);
v_parents_2094_ = lean_ctor_get(v_t_2092_, 1);
v_idxs_2095_ = lean_ctor_get(v_t_2092_, 2);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_array_get_size(v_parents_2094_);
v___x_2103_ = lean_nat_dec_lt(v___x_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
return v_t_2092_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
lean_inc_ref(v_idxs_2095_);
lean_inc_ref(v_parents_2094_);
lean_inc(v_cur_2093_);
lean_dec_ref(v_t_2092_);
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_array_get_size(v_idxs_2095_);
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_nat_sub(v___x_2105_, v___x_2106_);
v___x_2108_ = lean_array_get_borrowed(v___x_2101_, v_idxs_2095_, v___x_2107_);
lean_dec(v___x_2107_);
v___x_2109_ = lean_nat_sub(v___x_2102_, v___x_2106_);
v___x_2110_ = lean_array_get_borrowed(v___x_2104_, v_parents_2094_, v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = l_Lean_Syntax_getNumArgs(v___x_2110_);
v___x_2112_ = lean_nat_dec_lt(v___x_2108_, v___x_2111_);
lean_dec(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_dec(v_cur_2093_);
lean_inc(v___x_2110_);
v___y_2097_ = v___x_2110_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2113_; 
lean_inc(v___x_2110_);
v___x_2113_ = l_Lean_Syntax_setArg(v___x_2110_, v___x_2108_, v_cur_2093_);
v___y_2097_ = v___x_2113_;
goto v___jp_2096_;
}
}
v___jp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_array_pop(v_parents_2094_);
v___x_2099_ = lean_array_pop(v_idxs_2095_);
v___x_2100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2100_, 0, v___y_2097_);
lean_ctor_set(v___x_2100_, 1, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2114_){
_start:
{
lean_object* v_parents_2115_; lean_object* v_idxs_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v_parents_2115_ = lean_ctor_get(v_t_2114_, 1);
v_idxs_2116_ = lean_ctor_get(v_t_2114_, 2);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_array_get_size(v_parents_2115_);
v___x_2119_ = lean_nat_dec_lt(v___x_2117_, v___x_2118_);
if (v___x_2119_ == 0)
{
return v_t_2114_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_inc_ref(v_idxs_2116_);
v___x_2120_ = l_Lean_Syntax_Traverser_up(v_t_2114_);
v___x_2121_ = lean_array_get_size(v_idxs_2116_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_sub(v___x_2121_, v___x_2122_);
v___x_2124_ = lean_array_get(v___x_2117_, v_idxs_2116_, v___x_2123_);
lean_dec(v___x_2123_);
lean_dec_ref(v_idxs_2116_);
v___x_2125_ = lean_nat_sub(v___x_2124_, v___x_2122_);
lean_dec(v___x_2124_);
v___x_2126_ = l_Lean_Syntax_Traverser_down(v___x_2120_, v___x_2125_);
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2127_){
_start:
{
lean_object* v_parents_2128_; lean_object* v_idxs_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_parents_2128_ = lean_ctor_get(v_t_2127_, 1);
v_idxs_2129_ = lean_ctor_get(v_t_2127_, 2);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_array_get_size(v_parents_2128_);
v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
return v_t_2127_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_inc_ref(v_idxs_2129_);
v___x_2133_ = l_Lean_Syntax_Traverser_up(v_t_2127_);
v___x_2134_ = lean_array_get_size(v_idxs_2129_);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_sub(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_array_get(v___x_2130_, v_idxs_2129_, v___x_2136_);
lean_dec(v___x_2136_);
lean_dec_ref(v_idxs_2129_);
v___x_2138_ = lean_nat_add(v___x_2137_, v___x_2135_);
lean_dec(v___x_2137_);
v___x_2139_ = l_Lean_Syntax_Traverser_down(v___x_2133_, v___x_2138_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2140_){
_start:
{
lean_object* v_cur_2141_; 
v_cur_2141_ = lean_ctor_get(v_self_2140_, 0);
lean_inc(v_cur_2141_);
return v_cur_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2142_);
lean_dec_ref(v_self_2142_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2145_, lean_object* v_t_2146_){
_start:
{
lean_object* v_toApplicative_2147_; lean_object* v_toFunctor_2148_; lean_object* v_map_2149_; lean_object* v_get_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; 
v_toApplicative_2147_ = lean_ctor_get(v_inst_2145_, 0);
lean_inc_ref(v_toApplicative_2147_);
lean_dec_ref(v_inst_2145_);
v_toFunctor_2148_ = lean_ctor_get(v_toApplicative_2147_, 0);
lean_inc_ref(v_toFunctor_2148_);
lean_dec_ref(v_toApplicative_2147_);
v_map_2149_ = lean_ctor_get(v_toFunctor_2148_, 0);
lean_inc(v_map_2149_);
lean_dec_ref(v_toFunctor_2148_);
v_get_2150_ = lean_ctor_get(v_t_2146_, 0);
lean_inc(v_get_2150_);
lean_dec_ref(v_t_2146_);
v___f_2151_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2152_ = lean_apply_4(v_map_2149_, lean_box(0), lean_box(0), v___f_2151_, v_get_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2153_, lean_object* v_inst_2154_, lean_object* v_t_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2154_, v_t_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2157_, lean_object* v_s_2158_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = l_Lean_Syntax_Traverser_setCur(v_s_2158_, v_stx_2157_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2162_, lean_object* v_stx_2163_){
_start:
{
lean_object* v_modifyGet_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; 
v_modifyGet_2164_ = lean_ctor_get(v_t_2162_, 2);
lean_inc(v_modifyGet_2164_);
lean_dec_ref(v_t_2162_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2165_, 0, v_stx_2163_);
v___x_2166_ = lean_apply_2(v_modifyGet_2164_, lean_box(0), v___f_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2167_, lean_object* v_t_2168_, lean_object* v_stx_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2168_, v_stx_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2171_, lean_object* v_s_2172_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Lean_Syntax_Traverser_down(v_s_2172_, v_idx_2171_);
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2176_, lean_object* v_idx_2177_){
_start:
{
lean_object* v_modifyGet_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
v_modifyGet_2178_ = lean_ctor_get(v_t_2176_, 2);
lean_inc(v_modifyGet_2178_);
lean_dec_ref(v_t_2176_);
v___f_2179_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2179_, 0, v_idx_2177_);
v___x_2180_ = lean_apply_2(v_modifyGet_2178_, lean_box(0), v___f_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2181_, lean_object* v_t_2182_, lean_object* v_idx_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2182_, v_idx_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = l_Lean_Syntax_Traverser_up(v_s_2185_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2190_){
_start:
{
lean_object* v_modifyGet_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; 
v_modifyGet_2191_ = lean_ctor_get(v_t_2190_, 2);
lean_inc(v_modifyGet_2191_);
lean_dec_ref(v_t_2190_);
v___f_2192_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2193_ = lean_apply_2(v_modifyGet_2191_, lean_box(0), v___f_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2194_, lean_object* v_t_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2197_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = l_Lean_Syntax_Traverser_left(v_s_2197_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2202_){
_start:
{
lean_object* v_modifyGet_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
v_modifyGet_2203_ = lean_ctor_get(v_t_2202_, 2);
lean_inc(v_modifyGet_2203_);
lean_dec_ref(v_t_2202_);
v___f_2204_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2205_ = lean_apply_2(v_modifyGet_2203_, lean_box(0), v___f_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2206_, lean_object* v_t_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2209_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = l_Lean_Syntax_Traverser_right(v_s_2209_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2214_){
_start:
{
lean_object* v_modifyGet_2215_; lean_object* v___f_2216_; lean_object* v___x_2217_; 
v_modifyGet_2215_ = lean_ctor_get(v_t_2214_, 2);
lean_inc(v_modifyGet_2215_);
lean_dec_ref(v_t_2214_);
v___f_2216_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2217_ = lean_apply_2(v_modifyGet_2215_, lean_box(0), v___f_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2218_, lean_object* v_t_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2221_, lean_object* v_st_2222_){
_start:
{
lean_object* v_idxs_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v_idxs_2223_ = lean_ctor_get(v_st_2222_, 2);
v___x_2224_ = lean_array_get_size(v_idxs_2223_);
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_nat_sub(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_nat_dec_lt(v___x_2226_, v___x_2224_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v___x_2226_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_apply_2(v_toPure_2221_, lean_box(0), v___x_2228_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_array_fget_borrowed(v_idxs_2223_, v___x_2226_);
lean_dec(v___x_2226_);
lean_inc(v___x_2230_);
v___x_2231_ = lean_apply_2(v_toPure_2221_, lean_box(0), v___x_2230_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2232_, lean_object* v_st_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2232_, v_st_2233_);
lean_dec_ref(v_st_2233_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2235_, lean_object* v_t_2236_){
_start:
{
lean_object* v_toApplicative_2237_; lean_object* v_toBind_2238_; lean_object* v_get_2239_; lean_object* v_toPure_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; 
v_toApplicative_2237_ = lean_ctor_get(v_inst_2235_, 0);
lean_inc_ref(v_toApplicative_2237_);
v_toBind_2238_ = lean_ctor_get(v_inst_2235_, 1);
lean_inc(v_toBind_2238_);
lean_dec_ref(v_inst_2235_);
v_get_2239_ = lean_ctor_get(v_t_2236_, 0);
lean_inc(v_get_2239_);
lean_dec_ref(v_t_2236_);
v_toPure_2240_ = lean_ctor_get(v_toApplicative_2237_, 1);
lean_inc(v_toPure_2240_);
lean_dec_ref(v_toApplicative_2237_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2241_, 0, v_toPure_2240_);
v___x_2242_ = lean_apply_4(v_toBind_2238_, lean_box(0), lean_box(0), v_get_2239_, v___f_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2243_, lean_object* v_inst_2244_, lean_object* v_t_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2244_, v_t_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2247_, lean_object* v_i_2248_){
_start:
{
lean_object* v_args_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_args_2249_ = lean_ctor_get(v_n_2247_, 2);
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_array_get_borrowed(v___x_2250_, v_args_2249_, v_i_2248_);
v___x_2252_ = l_Lean_Syntax_getId(v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2253_, lean_object* v_i_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_SyntaxNode_getIdAt(v_n_2253_, v_i_2254_);
lean_dec(v_i_2254_);
lean_dec(v_n_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2258_ = lean_box(2);
v___x_2259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2257_);
lean_ctor_set(v___x_2259_, 2, v_args_2256_);
return v___x_2259_;
}
}
uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2265_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 1)
{
lean_object* v_kind_2266_; 
v_kind_2266_ = lean_ctor_get(v_x_2265_, 1);
if (lean_obj_tag(v_kind_2266_) == 1)
{
lean_object* v_pre_2267_; lean_object* v_str_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v_pre_2267_ = lean_ctor_get(v_kind_2266_, 0);
v_str_2268_ = lean_ctor_get(v_kind_2266_, 1);
v___x_2269_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2270_ = lean_string_dec_eq(v_str_2268_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2272_ = lean_string_dec_eq(v_str_2268_, v___x_2271_);
if (v___x_2272_ == 0)
{
return v___x_2272_;
}
else
{
if (lean_obj_tag(v_pre_2267_) == 1)
{
lean_object* v_pre_2273_; 
v_pre_2273_ = lean_ctor_get(v_pre_2267_, 0);
if (lean_obj_tag(v_pre_2273_) == 1)
{
lean_object* v_pre_2274_; 
v_pre_2274_ = lean_ctor_get(v_pre_2273_, 0);
if (lean_obj_tag(v_pre_2274_) == 1)
{
lean_object* v_pre_2275_; 
v_pre_2275_ = lean_ctor_get(v_pre_2274_, 0);
if (lean_obj_tag(v_pre_2275_) == 0)
{
lean_object* v_str_2276_; lean_object* v_str_2277_; lean_object* v_str_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_str_2276_ = lean_ctor_get(v_pre_2267_, 1);
v_str_2277_ = lean_ctor_get(v_pre_2273_, 1);
v_str_2278_ = lean_ctor_get(v_pre_2274_, 1);
v___x_2279_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2280_ = lean_string_dec_eq(v_str_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
return v___x_2270_;
}
else
{
lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2282_ = lean_string_dec_eq(v_str_2277_, v___x_2281_);
if (v___x_2282_ == 0)
{
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2284_ = lean_string_dec_eq(v_str_2276_, v___x_2283_);
return v___x_2284_;
}
}
}
else
{
return v___x_2270_;
}
}
else
{
return v___x_2270_;
}
}
else
{
return v___x_2270_;
}
}
else
{
return v___x_2270_;
}
}
}
else
{
return v___x_2270_;
}
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = 0;
return v___x_2285_;
}
}
else
{
uint8_t v___x_2286_; 
v___x_2286_ = 0;
return v___x_2286_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isQuot_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2265_ = stack[0].m_obj;
uint8_t v_res_2287_;
v_res_2287_ = l_Lean_Syntax_isQuot(v_x_2265_);
stack->m_num = v_res_2287_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2288_){
_start:
{
uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_res_2289_ = l_Lean_Syntax_isQuot(v_x_2288_);
lean_dec(v_x_2288_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___y_2300_; uint8_t v___x_2306_; 
v___x_2297_ = l_Lean_Syntax_getNumArgs(v_stx_2296_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2306_ = lean_nat_dec_eq(v___x_2297_, v___x_2298_);
lean_dec(v___x_2297_);
if (v___x_2306_ == 0)
{
v___y_2300_ = v_stx_2296_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2307_);
lean_dec(v_stx_2296_);
v___y_2300_ = v___x_2308_;
goto v___jp_2299_;
}
v___jp_2299_:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2300_);
v___x_2302_ = l_Lean_Syntax_isOfKind(v___y_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Syntax_getArg(v___y_2300_, v___x_2298_);
lean_dec(v___y_2300_);
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(3u);
v___x_2305_ = l_Lean_Syntax_getArg(v___y_2300_, v___x_2304_);
lean_dec(v___y_2300_);
return v___x_2305_;
}
}
}
}
uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2310_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 1)
{
lean_object* v_kind_2311_; 
v_kind_2311_ = lean_ctor_get(v_x_2310_, 1);
if (lean_obj_tag(v_kind_2311_) == 1)
{
lean_object* v_str_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_str_2312_ = lean_ctor_get(v_kind_2311_, 1);
v___x_2313_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2314_ = lean_string_dec_eq(v_str_2312_, v___x_2313_);
return v___x_2314_;
}
else
{
uint8_t v___x_2315_; 
v___x_2315_ = 0;
return v___x_2315_;
}
}
else
{
uint8_t v___x_2316_; 
v___x_2316_ = 0;
return v___x_2316_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2310_ = stack[0].m_obj;
uint8_t v_res_2317_;
v_res_2317_ = l_Lean_Syntax_isAntiquot(v_x_2310_);
stack->m_num = v_res_2317_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Lean_Syntax_isAntiquot(v_x_2318_);
lean_dec(v_x_2318_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2321_, uint8_t v___x_2322_, lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_eq(v_i_2324_, v_stop_2325_);
if (v___x_2326_ == 0)
{
uint8_t v___x_2327_; uint8_t v___y_2329_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2327_ = 1;
v___x_2333_ = lean_array_uget_borrowed(v_as_2323_, v_i_2324_);
v___x_2334_ = l_Lean_Syntax_isAntiquot(v___x_2333_);
if (v___x_2334_ == 0)
{
v___y_2329_ = v___y_2321_;
goto v___jp_2328_;
}
else
{
v___y_2329_ = v___x_2322_;
goto v___jp_2328_;
}
v___jp_2328_:
{
if (v___y_2329_ == 0)
{
size_t v___x_2330_; size_t v___x_2331_; 
v___x_2330_ = ((size_t)1ULL);
v___x_2331_ = lean_usize_add(v_i_2324_, v___x_2330_);
v_i_2324_ = v___x_2331_;
goto _start;
}
else
{
return v___x_2327_;
}
}
}
else
{
uint8_t v___x_2335_; 
v___x_2335_ = 0;
return v___x_2335_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_2321_ = stack[0].m_num;
uint8_t v___x_2322_ = stack[1].m_num;
lean_object* v_as_2323_ = stack[2].m_obj;
size_t v_i_2324_ = stack[3].m_num;
size_t v_stop_2325_ = stack[4].m_num;
uint8_t v_res_2336_;
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2321_, v___x_2322_, v_as_2323_, v_i_2324_, v_stop_2325_);
stack->m_num = v_res_2336_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2337_, lean_object* v___x_2338_, lean_object* v_as_2339_, lean_object* v_i_2340_, lean_object* v_stop_2341_){
_start:
{
uint8_t v___y_330__boxed_2342_; uint8_t v___x_331__boxed_2343_; size_t v_i_boxed_2344_; size_t v_stop_boxed_2345_; uint8_t v_res_2346_; lean_object* v_r_2347_; 
v___y_330__boxed_2342_ = lean_unbox(v___y_2337_);
v___x_331__boxed_2343_ = lean_unbox(v___x_2338_);
v_i_boxed_2344_ = lean_unbox_usize(v_i_2340_);
lean_dec(v_i_2340_);
v_stop_boxed_2345_ = lean_unbox_usize(v_stop_2341_);
lean_dec(v_stop_2341_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_330__boxed_2342_, v___x_331__boxed_2343_, v_as_2339_, v_i_boxed_2344_, v_stop_boxed_2345_);
lean_dec_ref(v_as_2339_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2348_){
_start:
{
uint8_t v___x_2349_; uint8_t v___y_2351_; 
v___x_2349_ = l_Lean_Syntax_isAntiquot(v_stx_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2348_);
v___x_2360_ = l_Lean_Syntax_isOfKind(v_stx_2348_, v___x_2359_);
if (v___x_2360_ == 0)
{
v___y_2351_ = v___x_2360_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = l_Lean_Syntax_getNumArgs(v_stx_2348_);
v___x_2363_ = lean_nat_dec_lt(v___x_2361_, v___x_2362_);
lean_dec(v___x_2362_);
v___y_2351_ = v___x_2363_;
goto v___jp_2350_;
}
}
else
{
lean_dec(v_stx_2348_);
return v___x_2349_;
}
v___jp_2350_:
{
if (v___y_2351_ == 0)
{
lean_dec(v_stx_2348_);
return v___y_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2352_ = l_Lean_Syntax_getArgs(v_stx_2348_);
lean_dec(v_stx_2348_);
v___x_2353_ = lean_unsigned_to_nat(0u);
v___x_2354_ = lean_array_get_size(v___x_2352_);
v___x_2355_ = lean_nat_dec_lt(v___x_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2352_);
return v___y_2351_;
}
else
{
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2352_);
return v___y_2351_;
}
else
{
size_t v___x_2356_; size_t v___x_2357_; uint8_t v___x_2358_; 
v___x_2356_ = ((size_t)0ULL);
v___x_2357_ = lean_usize_of_nat(v___x_2354_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2351_, v___x_2349_, v___x_2352_, v___x_2356_, v___x_2357_);
lean_dec_ref(v___x_2352_);
if (v___x_2358_ == 0)
{
return v___x_2355_;
}
else
{
return v___x_2349_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isAntiquots_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2348_ = stack[0].m_obj;
uint8_t v_res_2364_;
v_res_2364_ = l_Lean_Syntax_isAntiquots(v_stx_2348_);
stack->m_num = v_res_2364_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2365_){
_start:
{
uint8_t v_res_2366_; lean_object* v_r_2367_; 
v_res_2366_ = l_Lean_Syntax_isAntiquots(v_stx_2365_);
v_r_2367_ = lean_box(v_res_2366_);
return v_r_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2368_){
_start:
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2368_);
v___x_2370_ = l_Lean_Syntax_isOfKind(v_stx_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
return v_stx_2368_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = l_Lean_Syntax_getArg(v_stx_2368_, v___x_2371_);
lean_dec(v_stx_2368_);
return v___x_2372_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2375_ = l_Lean_mkAtom(v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2378_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2379_ = lean_unsigned_to_nat(4u);
v___x_2380_ = lean_mk_empty_array_with_capacity(v___x_2379_);
v___x_2381_ = lean_array_push(v___x_2380_, v___x_2378_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2390_ = l_Lean_mkAtom(v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2392_ = lean_unsigned_to_nat(2u);
v___x_2393_ = lean_mk_empty_array_with_capacity(v___x_2392_);
v___x_2394_ = lean_array_push(v___x_2393_, v___x_2391_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2406_ = l_Lean_mkAtom(v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2409_ = l_Lean_mkAtom(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2410_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2411_ = lean_unsigned_to_nat(3u);
v___x_2412_ = lean_mk_empty_array_with_capacity(v___x_2411_);
v___x_2413_ = lean_array_push(v___x_2412_, v___x_2410_);
return v___x_2413_;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2414_, lean_object* v_term_2415_, lean_object* v_nesting_2416_, lean_object* v_name_2417_, uint8_t v_isPseudoKind_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v_nesting_2423_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2442_; uint8_t v___x_2450_; 
v___x_2419_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2420_ = lean_mk_array(v_nesting_2416_, v___x_2419_);
v___x_2421_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2422_ = lean_box(2);
v_nesting_2423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2423_, 0, v___x_2422_);
lean_ctor_set(v_nesting_2423_, 1, v___x_2421_);
lean_ctor_set(v_nesting_2423_, 2, v___x_2420_);
v___x_2450_ = l_Lean_Syntax_isIdent(v_term_2415_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2415_);
v___x_2452_ = l_Lean_Syntax_isOfKind(v_term_2415_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2453_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2454_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2455_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2456_ = lean_array_push(v___x_2455_, v_term_2415_);
v___x_2457_ = lean_array_push(v___x_2456_, v___x_2454_);
v___x_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2422_);
lean_ctor_set(v___x_2458_, 1, v___x_2453_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
v___y_2442_ = v___x_2458_;
goto v___jp_2441_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
v___x_2460_ = l_Lean_Syntax_getArg(v_term_2415_, v___x_2459_);
lean_dec(v_term_2415_);
v___y_2442_ = v___x_2460_;
goto v___jp_2441_;
}
}
else
{
v___y_2442_ = v_term_2415_;
goto v___jp_2441_;
}
v___jp_2424_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_inc(v___y_2427_);
v___x_2428_ = l_Lean_Name_append(v_kind_2414_, v___y_2427_);
v___x_2429_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2430_ = l_Lean_Name_append(v___x_2428_, v___x_2429_);
v___x_2431_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2432_ = lean_array_push(v___x_2431_, v_nesting_2423_);
v___x_2433_ = lean_array_push(v___x_2432_, v___y_2426_);
v___x_2434_ = lean_array_push(v___x_2433_, v___y_2425_);
v___x_2435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2422_);
lean_ctor_set(v___x_2435_, 1, v___x_2430_);
lean_ctor_set(v___x_2435_, 2, v___x_2434_);
return v___x_2435_;
}
v___jp_2436_:
{
if (v_isPseudoKind_2418_ == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_box(0);
v___y_2425_ = v___y_2438_;
v___y_2426_ = v___y_2437_;
v___y_2427_ = v___x_2439_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2440_; 
v___x_2440_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2425_ = v___y_2438_;
v___y_2426_ = v___y_2437_;
v___y_2427_ = v___x_2440_;
goto v___jp_2424_;
}
}
v___jp_2441_:
{
if (lean_obj_tag(v_name_2417_) == 0)
{
lean_object* v___x_2443_; 
v___x_2443_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2437_ = v___y_2442_;
v___y_2438_ = v___x_2443_;
goto v___jp_2436_;
}
else
{
lean_object* v_val_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_val_2444_ = lean_ctor_get(v_name_2417_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v_name_2417_, 1);
v___x_2445_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2446_ = l_Lean_mkAtom(v_val_2444_);
v___x_2447_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2448_ = lean_array_push(v___x_2447_, v___x_2446_);
v___x_2449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2422_);
lean_ctor_set(v___x_2449_, 1, v___x_2445_);
lean_ctor_set(v___x_2449_, 2, v___x_2448_);
v___y_2437_ = v___y_2442_;
v___y_2438_ = v___x_2449_;
goto v___jp_2436_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_mkAntiquotNode_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_2414_ = stack[0].m_obj;
lean_object* v_term_2415_ = stack[1].m_obj;
lean_object* v_nesting_2416_ = stack[2].m_obj;
lean_object* v_name_2417_ = stack[3].m_obj;
uint8_t v_isPseudoKind_2418_ = stack[4].m_num;
lean_object* v_res_2461_;
v_res_2461_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2414_, v_term_2415_, v_nesting_2416_, v_name_2417_, v_isPseudoKind_2418_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2462_, lean_object* v_term_2463_, lean_object* v_nesting_2464_, lean_object* v_name_2465_, lean_object* v_isPseudoKind_2466_){
_start:
{
uint8_t v_isPseudoKind_boxed_2467_; lean_object* v_res_2468_; 
v_isPseudoKind_boxed_2467_ = lean_unbox(v_isPseudoKind_2466_);
v_res_2468_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2462_, v_term_2463_, v_nesting_2464_, v_name_2465_, v_isPseudoKind_boxed_2467_);
return v_res_2468_;
}
}
uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2470_ = lean_unsigned_to_nat(1u);
v___x_2471_ = l_Lean_Syntax_getArg(v_stx_2469_, v___x_2470_);
v___x_2472_ = l_Lean_Syntax_getArgs(v___x_2471_);
lean_dec(v___x_2471_);
v___x_2473_ = lean_array_get_size(v___x_2472_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = lean_nat_dec_eq(v___x_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
v___x_2476_ = 1;
return v___x_2476_;
}
else
{
uint8_t v___x_2477_; 
v___x_2477_ = 0;
return v___x_2477_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isEscapedAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2469_ = stack[0].m_obj;
uint8_t v_res_2478_;
v_res_2478_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2469_);
stack->m_num = v_res_2478_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2479_){
_start:
{
uint8_t v_res_2480_; lean_object* v_r_2481_; 
v_res_2480_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2479_);
lean_dec(v_stx_2479_);
v_r_2481_ = lean_box(v_res_2480_);
return v_r_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = l_Lean_Syntax_isAntiquot(v_stx_2482_);
if (v___x_2483_ == 0)
{
return v_stx_2482_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = l_Lean_Syntax_getArg(v_stx_2482_, v___x_2484_);
v___x_2486_ = l_Lean_Syntax_getArgs(v___x_2485_);
lean_dec(v___x_2485_);
v___x_2487_ = lean_array_pop(v___x_2486_);
v___x_2488_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2489_ = lean_box(2);
v___x_2490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2488_);
lean_ctor_set(v___x_2490_, 2, v___x_2487_);
v___x_2491_ = l_Lean_Syntax_setArg(v_stx_2482_, v___x_2484_, v___x_2490_);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2492_){
_start:
{
lean_object* v___y_2494_; uint8_t v___x_2505_; 
v___x_2505_ = l_Lean_Syntax_isAntiquot(v_stx_2492_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_unsigned_to_nat(3u);
v___x_2507_ = l_Lean_Syntax_getArg(v_stx_2492_, v___x_2506_);
v___y_2494_ = v___x_2507_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_unsigned_to_nat(2u);
v___x_2509_ = l_Lean_Syntax_getArg(v_stx_2492_, v___x_2508_);
v___y_2494_ = v___x_2509_;
goto v___jp_2493_;
}
v___jp_2493_:
{
uint8_t v___x_2495_; 
v___x_2495_ = l_Lean_Syntax_isIdent(v___y_2494_);
if (v___x_2495_ == 0)
{
uint8_t v___x_2496_; 
v___x_2496_ = l_Lean_Syntax_isAtom(v___y_2494_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v___x_2498_ = l_Lean_Syntax_getArg(v___y_2494_, v___x_2497_);
lean_dec(v___y_2494_);
return v___x_2498_;
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2499_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = lean_mk_empty_array_with_capacity(v___x_2500_);
v___x_2502_ = lean_array_push(v___x_2501_, v___y_2494_);
v___x_2503_ = lean_box(2);
v___x_2504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2499_);
lean_ctor_set(v___x_2504_, 2, v___x_2502_);
return v___x_2504_;
}
}
else
{
return v___y_2494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2510_);
lean_dec(v_stx_2510_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2512_){
_start:
{
if (lean_obj_tag(v_x_2512_) == 1)
{
lean_object* v_kind_2513_; 
v_kind_2513_ = lean_ctor_get(v_x_2512_, 1);
if (lean_obj_tag(v_kind_2513_) == 1)
{
lean_object* v_pre_2514_; lean_object* v_str_2515_; 
v_pre_2514_ = lean_ctor_get(v_kind_2513_, 0);
v_str_2515_ = lean_ctor_get(v_kind_2513_, 1);
if (lean_obj_tag(v_pre_2514_) == 1)
{
lean_object* v_pre_2521_; lean_object* v_str_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v_pre_2521_ = lean_ctor_get(v_pre_2514_, 0);
v_str_2522_ = lean_ctor_get(v_pre_2514_, 1);
v___x_2523_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2524_ = lean_string_dec_eq(v_str_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2526_ = lean_string_dec_eq(v_str_2515_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_box(0);
return v___x_2527_;
}
else
{
goto v___jp_2516_;
}
}
else
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2529_ = lean_string_dec_eq(v_str_2515_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_box(0);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_box(v___x_2529_);
lean_inc(v_pre_2521_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_pre_2521_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
}
}
else
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2535_ = lean_string_dec_eq(v_str_2515_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_box(0);
return v___x_2536_;
}
else
{
goto v___jp_2516_;
}
}
v___jp_2516_:
{
uint8_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = 0;
v___x_2518_ = lean_box(v___x_2517_);
lean_inc(v_pre_2514_);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_pre_2514_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_box(0);
return v___x_2537_;
}
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_box(0);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2539_);
lean_dec(v_x_2539_);
return v_res_2540_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2541_, size_t v_i_2542_, size_t v_stop_2543_, lean_object* v_b_2544_){
_start:
{
lean_object* v___y_2546_; uint8_t v___x_2550_; 
v___x_2550_ = lean_usize_dec_eq(v_i_2542_, v_stop_2543_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_array_uget_borrowed(v_as_2541_, v_i_2542_);
v___x_2552_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2551_);
if (lean_obj_tag(v___x_2552_) == 0)
{
v___y_2546_ = v_b_2544_;
goto v___jp_2545_;
}
else
{
lean_object* v_val_2553_; lean_object* v___x_2554_; 
v_val_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = lean_array_push(v_b_2544_, v_val_2553_);
v___y_2546_ = v___x_2554_;
goto v___jp_2545_;
}
}
else
{
return v_b_2544_;
}
v___jp_2545_:
{
size_t v___x_2547_; size_t v___x_2548_; 
v___x_2547_ = ((size_t)1ULL);
v___x_2548_ = lean_usize_add(v_i_2542_, v___x_2547_);
v_i_2542_ = v___x_2548_;
v_b_2544_ = v___y_2546_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2541_ = stack[0].m_obj;
size_t v_i_2542_ = stack[1].m_num;
size_t v_stop_2543_ = stack[2].m_num;
lean_object* v_b_2544_ = stack[3].m_obj;
lean_object* v_res_2555_;
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2541_, v_i_2542_, v_stop_2543_, v_b_2544_);
stack->m_obj
 = v_res_2555_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2556_, lean_object* v_i_2557_, lean_object* v_stop_2558_, lean_object* v_b_2559_){
_start:
{
size_t v_i_boxed_2560_; size_t v_stop_boxed_2561_; lean_object* v_res_2562_; 
v_i_boxed_2560_ = lean_unbox_usize(v_i_2557_);
lean_dec(v_i_2557_);
v_stop_boxed_2561_ = lean_unbox_usize(v_stop_2558_);
lean_dec(v_stop_2558_);
v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2556_, v_i_boxed_2560_, v_stop_boxed_2561_, v_b_2559_);
lean_dec_ref(v_as_2556_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2565_, lean_object* v_start_2566_, lean_object* v_stop_2567_){
_start:
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2569_ = lean_nat_dec_lt(v_start_2566_, v_stop_2567_);
if (v___x_2569_ == 0)
{
return v___x_2568_;
}
else
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = lean_array_get_size(v_as_2565_);
v___x_2571_ = lean_nat_dec_le(v_stop_2567_, v___x_2570_);
if (v___x_2571_ == 0)
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_lt(v_start_2566_, v___x_2570_);
if (v___x_2572_ == 0)
{
return v___x_2568_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_usize_of_nat(v_start_2566_);
v___x_2574_ = lean_usize_of_nat(v___x_2570_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2565_, v___x_2573_, v___x_2574_, v___x_2568_);
return v___x_2575_;
}
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_usize_of_nat(v_start_2566_);
v___x_2577_ = lean_usize_of_nat(v_stop_2567_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2565_, v___x_2576_, v___x_2577_, v___x_2568_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2579_, lean_object* v_start_2580_, lean_object* v_stop_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2579_, v_start_2580_, v_stop_2581_);
lean_dec(v_stop_2581_);
lean_dec(v_start_2580_);
lean_dec_ref(v_as_2579_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2583_){
_start:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2583_);
v___x_2585_ = l_Lean_Syntax_isOfKind(v_stx_2583_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2583_);
lean_dec(v_stx_2583_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_box(0);
return v___x_2587_;
}
else
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_val_2588_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2589_ = lean_box(0);
v___x_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_val_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
return v___x_2590_;
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2591_ = l_Lean_Syntax_getArgs(v_stx_2583_);
lean_dec(v_stx_2583_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_array_get_size(v___x_2591_);
v___x_2594_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2591_, v___x_2592_, v___x_2593_);
lean_dec_ref(v___x_2591_);
v___x_2595_ = lean_array_to_list(v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2597_){
_start:
{
if (lean_obj_tag(v_x_2597_) == 1)
{
lean_object* v_kind_2598_; 
v_kind_2598_ = lean_ctor_get(v_x_2597_, 1);
if (lean_obj_tag(v_kind_2598_) == 1)
{
lean_object* v_pre_2599_; lean_object* v_str_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_pre_2599_ = lean_ctor_get(v_kind_2598_, 0);
v_str_2600_ = lean_ctor_get(v_kind_2598_, 1);
v___x_2601_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2602_ = lean_string_dec_eq(v_str_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_box(0);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; 
lean_inc(v_pre_2599_);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_pre_2599_);
return v___x_2604_;
}
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_box(0);
return v___x_2605_;
}
}
else
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_box(0);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2607_);
lean_dec(v_x_2607_);
return v_res_2608_;
}
}
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2609_);
if (lean_obj_tag(v___x_2610_) == 0)
{
uint8_t v___x_2611_; 
v___x_2611_ = 0;
return v___x_2611_;
}
else
{
uint8_t v___x_2612_; 
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = 1;
return v___x_2612_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isAntiquotSplice_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2609_ = stack[0].m_obj;
uint8_t v_res_2613_;
v_res_2613_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2609_);
stack->m_num = v_res_2613_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2614_){
_start:
{
uint8_t v_res_2615_; lean_object* v_r_2616_; 
v_res_2615_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2614_);
lean_dec(v_stx_2614_);
v_r_2616_ = lean_box(v_res_2615_);
return v_r_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_unsigned_to_nat(3u);
v___x_2619_ = l_Lean_Syntax_getArg(v_stx_2617_, v___x_2618_);
v___x_2620_ = l_Lean_Syntax_getArgs(v___x_2619_);
lean_dec(v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2621_);
lean_dec(v_stx_2621_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2623_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_unsigned_to_nat(1u);
v___x_2626_ = l_Lean_Syntax_getArg(v_stx_2623_, v___x_2625_);
return v___x_2626_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = lean_unsigned_to_nat(5u);
v___x_2628_ = l_Lean_Syntax_getArg(v_stx_2623_, v___x_2627_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2629_);
lean_dec(v_stx_2629_);
return v_res_2630_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2636_ = l_Lean_mkAtom(v___x_2635_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2639_ = l_Lean_mkAtom(v___x_2638_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2641_ = lean_unsigned_to_nat(6u);
v___x_2642_ = lean_mk_empty_array_with_capacity(v___x_2641_);
v___x_2643_ = lean_array_push(v___x_2642_, v___x_2640_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2644_, lean_object* v_contents_2645_, lean_object* v_suffix_2646_, lean_object* v_nesting_2647_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_nesting_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2648_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2649_ = lean_mk_array(v_nesting_2647_, v___x_2648_);
v___x_2650_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2651_ = lean_box(2);
v_nesting_2652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2652_, 0, v___x_2651_);
lean_ctor_set(v_nesting_2652_, 1, v___x_2650_);
lean_ctor_set(v_nesting_2652_, 2, v___x_2649_);
v___x_2653_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2654_ = l_Lean_Name_append(v_kind_2644_, v___x_2653_);
v___x_2655_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2651_);
lean_ctor_set(v___x_2656_, 1, v___x_2650_);
lean_ctor_set(v___x_2656_, 2, v_contents_2645_);
v___x_2657_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2658_ = l_Lean_mkAtom(v_suffix_2646_);
v___x_2659_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2660_ = lean_array_push(v___x_2659_, v_nesting_2652_);
v___x_2661_ = lean_array_push(v___x_2660_, v___x_2655_);
v___x_2662_ = lean_array_push(v___x_2661_, v___x_2656_);
v___x_2663_ = lean_array_push(v___x_2662_, v___x_2657_);
v___x_2664_ = lean_array_push(v___x_2663_, v___x_2658_);
v___x_2665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2651_);
lean_ctor_set(v___x_2665_, 1, v___x_2654_);
lean_ctor_set(v___x_2665_, 2, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2667_){
_start:
{
if (lean_obj_tag(v_x_2667_) == 1)
{
lean_object* v_kind_2668_; 
v_kind_2668_ = lean_ctor_get(v_x_2667_, 1);
if (lean_obj_tag(v_kind_2668_) == 1)
{
lean_object* v_pre_2669_; lean_object* v_str_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v_pre_2669_ = lean_ctor_get(v_kind_2668_, 0);
v_str_2670_ = lean_ctor_get(v_kind_2668_, 1);
v___x_2671_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2672_ = lean_string_dec_eq(v_str_2670_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_box(0);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; 
lean_inc(v_pre_2669_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_pre_2669_);
return v___x_2674_;
}
}
else
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_box(0);
return v___x_2675_;
}
}
else
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_box(0);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2677_);
lean_dec(v_x_2677_);
return v_res_2678_;
}
}
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
uint8_t v___x_2681_; 
v___x_2681_ = 0;
return v___x_2681_;
}
else
{
uint8_t v___x_2682_; 
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = 1;
return v___x_2682_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isAntiquotSuffixSplice_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2679_ = stack[0].m_obj;
uint8_t v_res_2683_;
v_res_2683_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2679_);
stack->m_num = v_res_2683_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2684_){
_start:
{
uint8_t v_res_2685_; lean_object* v_r_2686_; 
v_res_2685_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2684_);
lean_dec(v_stx_2684_);
v_r_2686_ = lean_box(v_res_2685_);
return v_r_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2687_){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = l_Lean_Syntax_getArg(v_stx_2687_, v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2690_);
lean_dec(v_stx_2690_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2694_, lean_object* v_inner_2695_, lean_object* v_suffix_2696_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2697_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2698_ = l_Lean_Name_append(v_kind_2694_, v___x_2697_);
v___x_2699_ = l_Lean_mkAtom(v_suffix_2696_);
v___x_2700_ = lean_unsigned_to_nat(2u);
v___x_2701_ = lean_mk_empty_array_with_capacity(v___x_2700_);
v___x_2702_ = lean_array_push(v___x_2701_, v_inner_2695_);
v___x_2703_ = lean_array_push(v___x_2702_, v___x_2699_);
v___x_2704_ = lean_box(2);
v___x_2705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2698_);
lean_ctor_set(v___x_2705_, 2, v___x_2703_);
return v___x_2705_;
}
}
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2709_){
_start:
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2711_ = l_Lean_Syntax_isOfKind(v_stx_2709_, v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT void l_Lean_Syntax_isTokenAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2709_ = stack[0].m_obj;
uint8_t v_res_2712_;
v_res_2712_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2709_);
stack->m_num = v_res_2712_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2713_){
_start:
{
uint8_t v_res_2714_; lean_object* v_r_2715_; 
v_res_2714_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2713_);
v_r_2715_ = lean_box(v_res_2714_);
return v_r_2715_;
}
}
uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2716_){
_start:
{
uint8_t v___y_2718_; uint8_t v___x_2721_; 
v___x_2721_ = l_Lean_Syntax_isAntiquot(v_stx_2716_);
if (v___x_2721_ == 0)
{
uint8_t v___x_2722_; 
v___x_2722_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2716_);
v___y_2718_ = v___x_2722_;
goto v___jp_2717_;
}
else
{
v___y_2718_ = v___x_2721_;
goto v___jp_2717_;
}
v___jp_2717_:
{
if (v___y_2718_ == 0)
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2716_);
if (v___x_2719_ == 0)
{
uint8_t v___x_2720_; 
v___x_2720_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2716_);
return v___x_2720_;
}
else
{
lean_dec(v_stx_2716_);
return v___x_2719_;
}
}
else
{
lean_dec(v_stx_2716_);
return v___y_2718_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isAnyAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2716_ = stack[0].m_obj;
uint8_t v_res_2723_;
v_res_2723_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2716_);
stack->m_num = v_res_2723_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2724_){
_start:
{
uint8_t v_res_2725_; lean_object* v_r_2726_; 
v_res_2725_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2724_);
v_r_2726_ = lean_box(v_res_2725_);
return v_r_2726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2730_, lean_object* v_stx_2731_, lean_object* v_visit_2732_, lean_object* v_stack_2733_, lean_object* v_accept_2734_, lean_object* v_a_2735_, lean_object* v_b_2736_){
_start:
{
lean_object* v_a_2738_; uint8_t v___x_2742_; 
v___x_2742_ = lean_nat_dec_lt(v_a_2735_, v_upperBound_2730_);
if (v___x_2742_ == 0)
{
lean_dec(v_a_2735_);
lean_dec_ref(v_accept_2734_);
lean_dec(v_stack_2733_);
lean_dec_ref(v_visit_2732_);
lean_dec(v_stx_2731_);
lean_inc_ref(v_b_2736_);
return v_b_2736_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2745_ = l_Lean_Syntax_getArg(v_stx_2731_, v_a_2735_);
lean_inc_ref(v_visit_2732_);
lean_inc(v___x_2745_);
v___x_2746_ = lean_apply_1(v_visit_2732_, v___x_2745_);
v___x_2747_ = lean_unbox(v___x_2746_);
if (v___x_2747_ == 0)
{
lean_dec(v___x_2745_);
v_a_2738_ = v___x_2744_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_inc(v_a_2735_);
lean_inc(v_stx_2731_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v_stx_2731_);
lean_ctor_set(v___x_2748_, 1, v_a_2735_);
lean_inc(v_stack_2733_);
v___x_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_stack_2733_);
lean_inc_ref(v_accept_2734_);
lean_inc_ref(v_visit_2732_);
v___x_2750_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2732_, v_accept_2734_, v___x_2749_, v___x_2745_);
if (lean_obj_tag(v___x_2750_) == 1)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec(v_a_2735_);
lean_dec_ref(v_accept_2734_);
lean_dec(v_stack_2733_);
lean_dec_ref(v_visit_2732_);
lean_dec(v_stx_2731_);
v___x_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___x_2743_);
return v___x_2752_;
}
else
{
lean_dec(v___x_2750_);
v_a_2738_ = v___x_2744_;
goto v___jp_2737_;
}
}
}
v___jp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_add(v_a_2735_, v___x_2739_);
lean_dec(v_a_2735_);
v_a_2735_ = v___x_2740_;
v_b_2736_ = v_a_2738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2753_, lean_object* v_accept_2754_, lean_object* v_stack_2755_, lean_object* v_stx_2756_){
_start:
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
lean_inc_ref(v_accept_2754_);
lean_inc(v_stx_2756_);
v___x_2757_ = lean_apply_1(v_accept_2754_, v_stx_2756_);
v___x_2758_ = lean_unbox(v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v_fst_2764_; 
v___x_2759_ = l_Lean_Syntax_getNumArgs(v_stx_2756_);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_box(0);
v___x_2762_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2759_, v_stx_2756_, v_visit_2753_, v_stack_2755_, v_accept_2754_, v___x_2760_, v___x_2762_);
lean_dec(v___x_2759_);
v_fst_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_fst_2764_);
lean_dec_ref(v___x_2763_);
if (lean_obj_tag(v_fst_2764_) == 0)
{
return v___x_2761_;
}
else
{
lean_object* v_val_2765_; 
v_val_2765_ = lean_ctor_get(v_fst_2764_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v_fst_2764_, 1);
return v_val_2765_;
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec_ref(v_accept_2754_);
lean_dec_ref(v_visit_2753_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_stx_2756_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v_stack_2755_);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2770_, lean_object* v_stx_2771_, lean_object* v_visit_2772_, lean_object* v_stack_2773_, lean_object* v_accept_2774_, lean_object* v_a_2775_, lean_object* v_b_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2770_, v_stx_2771_, v_visit_2772_, v_stack_2773_, v_accept_2774_, v_a_2775_, v_b_2776_);
lean_dec_ref(v_b_2776_);
lean_dec(v_upperBound_2770_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2778_, lean_object* v_stx_2779_, lean_object* v_visit_2780_, lean_object* v_stack_2781_, lean_object* v_accept_2782_, lean_object* v_inst_2783_, lean_object* v_R_2784_, lean_object* v_a_2785_, lean_object* v_b_2786_, lean_object* v_c_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2778_, v_stx_2779_, v_visit_2780_, v_stack_2781_, v_accept_2782_, v_a_2785_, v_b_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2789_, lean_object* v_stx_2790_, lean_object* v_visit_2791_, lean_object* v_stack_2792_, lean_object* v_accept_2793_, lean_object* v_inst_2794_, lean_object* v_R_2795_, lean_object* v_a_2796_, lean_object* v_b_2797_, lean_object* v_c_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2789_, v_stx_2790_, v_visit_2791_, v_stack_2792_, v_accept_2793_, v_inst_2794_, v_R_2795_, v_a_2796_, v_b_2797_, v_c_2798_);
lean_dec_ref(v_b_2797_);
lean_dec(v_upperBound_2789_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2800_, lean_object* v_visit_2801_, lean_object* v_accept_2802_){
_start:
{
lean_object* v___x_2803_; uint8_t v___x_2804_; 
lean_inc_ref(v_visit_2801_);
lean_inc(v_root_2800_);
v___x_2803_ = lean_apply_1(v_visit_2801_, v_root_2800_);
v___x_2804_ = lean_unbox(v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_dec_ref(v_accept_2802_);
lean_dec_ref(v_visit_2801_);
lean_dec(v_root_2800_);
v___x_2805_ = lean_box(0);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_box(0);
v___x_2807_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2801_, v_accept_2802_, v___x_2806_, v_root_2800_);
return v___x_2807_;
}
}
}
uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2808_, lean_object* v_x_2809_, lean_object* v_p_2810_){
_start:
{
if (lean_obj_tag(v_p_2810_) == 0)
{
lean_dec_ref(v_x_2809_);
return v___x_2808_;
}
else
{
lean_object* v_fst_2811_; lean_object* v_val_2812_; uint8_t v___x_2813_; 
v_fst_2811_ = lean_ctor_get(v_x_2809_, 0);
lean_inc(v_fst_2811_);
lean_dec_ref(v_x_2809_);
v_val_2812_ = lean_ctor_get(v_p_2810_, 0);
v___x_2813_ = l_Lean_Syntax_isOfKind(v_fst_2811_, v_val_2812_);
return v___x_2813_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_Stack_matches___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2808_ = stack[0].m_num;
lean_object* v_x_2809_ = stack[1].m_obj;
lean_object* v_p_2810_ = stack[2].m_obj;
uint8_t v_res_2814_;
v_res_2814_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_2808_, v_x_2809_, v_p_2810_);
stack->m_num = v_res_2814_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2815_, lean_object* v_x_2816_, lean_object* v_p_2817_){
_start:
{
uint8_t v___x_123__boxed_2818_; uint8_t v_res_2819_; lean_object* v_r_2820_; 
v___x_123__boxed_2818_ = lean_unbox(v___x_2815_);
v_res_2819_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2818_, v_x_2816_, v_p_2817_);
lean_dec(v_p_2817_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2821_){
_start:
{
if (lean_obj_tag(v_x_2821_) == 0)
{
uint8_t v___x_2822_; 
v___x_2822_ = 1;
return v___x_2822_;
}
else
{
lean_object* v_head_2823_; uint8_t v___x_2824_; 
v_head_2823_ = lean_ctor_get(v_x_2821_, 0);
v___x_2824_ = lean_unbox(v_head_2823_);
if (v___x_2824_ == 0)
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_unbox(v_head_2823_);
return v___x_2825_;
}
else
{
lean_object* v_tail_2826_; 
v_tail_2826_ = lean_ctor_get(v_x_2821_, 1);
v_x_2821_ = v_tail_2826_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Lean_Syntax_Stack_matches_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2821_ = stack[0].m_obj;
uint8_t v_res_2828_;
v_res_2828_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2821_);
stack->m_num = v_res_2828_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2829_){
_start:
{
uint8_t v_res_2830_; lean_object* v_r_2831_; 
v_res_2830_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2829_);
lean_dec(v_x_2829_);
v_r_2831_ = lean_box(v_res_2830_);
return v_r_2831_;
}
}
uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2834_, lean_object* v_pattern_2835_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2836_ = l_List_lengthTR___redArg(v_pattern_2835_);
v___x_2837_ = l_List_lengthTR___redArg(v_stack_2834_);
v___x_2838_ = lean_nat_dec_le(v___x_2836_, v___x_2837_);
lean_dec(v___x_2837_);
lean_dec(v___x_2836_);
if (v___x_2838_ == 0)
{
lean_dec(v_pattern_2835_);
lean_dec(v_stack_2834_);
return v___x_2838_;
}
else
{
lean_object* v___x_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2839_ = lean_box(v___x_2838_);
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2840_, 0, v___x_2839_);
v___x_2841_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2842_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2840_, v_stack_2834_, v_pattern_2835_, v___x_2841_);
v___x_2843_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2842_);
lean_dec(v___x_2842_);
return v___x_2843_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_Stack_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_stack_2834_ = stack[0].m_obj;
lean_object* v_pattern_2835_ = stack[1].m_obj;
uint8_t v_res_2844_;
v_res_2844_ = l_Lean_Syntax_Stack_matches(v_stack_2834_, v_pattern_2835_);
stack->m_num = v_res_2844_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2845_, lean_object* v_pattern_2846_){
_start:
{
uint8_t v_res_2847_; lean_object* v_r_2848_; 
v_res_2847_ = l_Lean_Syntax_Stack_matches(v_stack_2845_, v_pattern_2846_);
v_r_2848_ = lean_box(v_res_2847_);
return v_r_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2849_, lean_object* v_trailing_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2849_);
if (lean_obj_tag(v___x_2851_) == 1)
{
lean_object* v_val_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2887_; 
v_val_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2887_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_val_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2887_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
if (lean_obj_tag(v_val_2852_) == 0)
{
lean_object* v_trailing_2856_; lean_object* v_leading_2857_; lean_object* v_pos_2858_; lean_object* v_endPos_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2885_; 
v_trailing_2856_ = lean_ctor_get(v_val_2852_, 2);
v_leading_2857_ = lean_ctor_get(v_val_2852_, 0);
v_pos_2858_ = lean_ctor_get(v_val_2852_, 1);
v_endPos_2859_ = lean_ctor_get(v_val_2852_, 3);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_val_2852_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2861_ = v_val_2852_;
v_isShared_2862_ = v_isSharedCheck_2885_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_endPos_2859_);
lean_inc(v_trailing_2856_);
lean_inc(v_pos_2858_);
lean_inc(v_leading_2857_);
lean_dec(v_val_2852_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2885_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_str_2863_; lean_object* v_startPos_2864_; lean_object* v_stopPos_2865_; lean_object* v_startPos_2866_; lean_object* v_stopPos_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2883_; 
v_str_2863_ = lean_ctor_get(v_trailing_2856_, 0);
lean_inc_ref(v_str_2863_);
v_startPos_2864_ = lean_ctor_get(v_trailing_2856_, 1);
lean_inc(v_startPos_2864_);
v_stopPos_2865_ = lean_ctor_get(v_trailing_2856_, 2);
lean_inc(v_stopPos_2865_);
lean_dec_ref(v_trailing_2856_);
v_startPos_2866_ = lean_ctor_get(v_trailing_2850_, 1);
v_stopPos_2867_ = lean_ctor_get(v_trailing_2850_, 2);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_trailing_2850_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v_trailing_2850_, 0);
lean_dec(v_unused_2884_);
v___x_2869_ = v_trailing_2850_;
v_isShared_2870_ = v_isSharedCheck_2883_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_stopPos_2867_);
lean_inc(v_startPos_2866_);
lean_dec(v_trailing_2850_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2883_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
uint8_t v_decide_2871_; 
v_decide_2871_ = lean_nat_dec_eq(v_stopPos_2865_, v_startPos_2866_);
lean_dec(v_startPos_2866_);
lean_dec(v_stopPos_2865_);
if (v_decide_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_del_object(v___x_2869_);
lean_dec(v_stopPos_2867_);
lean_dec(v_startPos_2864_);
lean_dec_ref(v_str_2863_);
lean_del_object(v___x_2861_);
lean_dec(v_endPos_2859_);
lean_dec(v_pos_2858_);
lean_dec_ref(v_leading_2857_);
lean_del_object(v___x_2854_);
lean_dec(v_stx_2849_);
v___x_2872_ = lean_box(0);
return v___x_2872_;
}
else
{
lean_object* v_trailing_2874_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v_startPos_2864_);
lean_ctor_set(v___x_2869_, 0, v_str_2863_);
v_trailing_2874_ = v___x_2869_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_str_2863_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_startPos_2864_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_stopPos_2867_);
v_trailing_2874_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 2, v_trailing_2874_);
v___x_2876_ = v___x_2861_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_leading_2857_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_pos_2858_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_trailing_2874_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_endPos_2859_);
v___x_2876_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = l_Lean_Syntax_setTailInfo(v_stx_2849_, v___x_2876_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2877_);
v___x_2879_ = v___x_2854_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2886_; 
lean_del_object(v___x_2854_);
lean_dec(v_val_2852_);
lean_dec_ref(v_trailing_2850_);
lean_dec(v_stx_2849_);
v___x_2886_ = lean_box(0);
return v___x_2886_;
}
}
}
else
{
lean_object* v___x_2888_; 
lean_dec(v___x_2851_);
lean_dec_ref(v_trailing_2850_);
lean_dec(v_stx_2849_);
v___x_2888_ = lean_box(0);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2889_, lean_object* v_trailing_2890_){
_start:
{
lean_object* v___x_2891_; 
lean_inc(v_stx_2889_);
v___x_2891_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2889_, v_trailing_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
return v_stx_2889_;
}
else
{
lean_object* v_val_2892_; 
lean_dec(v_stx_2889_);
v_val_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_val_2892_);
lean_dec_ref_known(v___x_2891_, 1);
return v_val_2892_;
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

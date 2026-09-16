// Lean compiler output
// Module: Lean.Widget.TaggedText
// Imports: public import Lean.Server.Rpc.Basic import Init.Data.Array.GetLit import Init.Data.String.Length
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object*);
uint8_t l_Std_Format_instBEqFlattenBehavior_beq(uint8_t, uint8_t);
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_posof(lean_object*, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_text_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_append_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_append_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_tag_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_tag_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Widget_instInhabitedTaggedText_default___closed__0 = (const lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instInhabitedTaggedText_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)}};
static const lean_object* l_Lean_Widget_instInhabitedTaggedText_default___closed__1 = (const lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object*);
static lean_once_cell_t l_Lean_Widget_instInhabitedTaggedText___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedTaggedText___closed__0;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Widget.TaggedText.text"};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3;
static lean_once_cell_t l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4;
static const lean_string_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Widget.TaggedText.append"};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7_value;
static const lean_string_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Widget.TaggedText.tag"};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value)}};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1_value;
static const lean_string_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2_value;
static const lean_string_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3_value;
static const lean_string_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4_value;
static const lean_string_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value)}};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19_value;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20_value;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30;
static lean_once_cell_t l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31;
static const lean_closure_object l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32 = (const lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32_value;
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)}};
static const lean_object* l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0 = (const lean_object*)&l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value;
static const lean_ctor_object l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1 = (const lean_object*)&l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_TaggedText_instInhabitedTaggedState_default = (const lean_object*)&l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState = (const lean_object*)&l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value)} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_get, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value;
static const lean_closure_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value),((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value)} };
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value;
static const lean_ctor_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value),((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value),((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value),((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value),((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value)}};
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value;
LEAN_EXPORT const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unreachable"};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Widget_TaggedText_ctorIdx___redArg(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx(lean_object* v_00_u03b1_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Widget_TaggedText_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___boxed(lean_object* v_00_u03b1_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Widget_TaggedText_ctorIdx(v_00_u03b1_10_, v_x_11_);
lean_dec_ref(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
if (lean_obj_tag(v_t_13_) == 2)
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_a_16_);
lean_dec_ref_known(v_t_13_, 2);
v___x_17_ = lean_apply_2(v_k_14_, v_a_15_, v_a_16_);
return v___x_17_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_18_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_18_);
lean_dec_ref(v_t_13_);
v___x_19_ = lean_apply_1(v_k_14_, v_a_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim(lean_object* v_00_u03b1_20_, lean_object* v_motive__1_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim___boxed(lean_object* v_00_u03b1_27_, lean_object* v_motive__1_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Widget_TaggedText_ctorElim(v_00_u03b1_27_, v_motive__1_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_text_elim___redArg(lean_object* v_t_34_, lean_object* v_text_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_34_, v_text_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_text_elim(lean_object* v_00_u03b1_37_, lean_object* v_motive__1_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_text_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_39_, v_text_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_append_elim___redArg(lean_object* v_t_43_, lean_object* v_append_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_43_, v_append_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_append_elim(lean_object* v_00_u03b1_46_, lean_object* v_motive__1_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_append_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_48_, v_append_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_tag_elim___redArg(lean_object* v_t_52_, lean_object* v_tag_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_52_, v_tag_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_tag_elim(lean_object* v_00_u03b1_55_, lean_object* v_motive__1_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_tag_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_57_, v_tag_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object* v_00_u03b1_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__1));
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedTaggedText___closed__0(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText(lean_object* v_a_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText___closed__0, &l_Lean_Widget_instInhabitedTaggedText___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText___closed__0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed(lean_object* v_inst_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_69_, v_x_70_, v_x_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq___redArg(lean_object* v_inst_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
lean_dec_ref(v_inst_74_);
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_a_78_; uint8_t v___x_79_; 
v_a_77_ = lean_ctor_get(v_x_75_, 0);
lean_inc_ref(v_a_77_);
lean_dec_ref_known(v_x_75_, 1);
v_a_78_ = lean_ctor_get(v_x_76_, 0);
lean_inc_ref(v_a_78_);
lean_dec_ref_known(v_x_76_, 1);
v___x_79_ = lean_string_dec_eq(v_a_77_, v_a_78_);
lean_dec_ref(v_a_78_);
lean_dec_ref(v_a_77_);
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
lean_dec_ref_known(v_x_75_, 1);
lean_dec_ref(v_x_76_);
v___x_80_ = 0;
return v___x_80_;
}
}
case 1:
{
if (lean_obj_tag(v_x_76_) == 1)
{
lean_object* v_a_81_; lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_a_81_ = lean_ctor_get(v_x_75_, 0);
lean_inc_ref(v_a_81_);
lean_dec_ref_known(v_x_75_, 1);
v_a_82_ = lean_ctor_get(v_x_76_, 0);
lean_inc_ref(v_a_82_);
lean_dec_ref_known(v_x_76_, 1);
v___x_83_ = lean_array_get_size(v_a_81_);
v___x_84_ = lean_array_get_size(v_a_82_);
v___x_85_ = lean_nat_dec_eq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_dec_ref(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec_ref(v_inst_74_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_86_, 0, v_inst_74_);
v___x_87_ = l_Array_isEqvAux___redArg(v_a_81_, v_a_82_, v___x_86_, v___x_83_);
lean_dec_ref(v_a_82_);
lean_dec_ref(v_a_81_);
return v___x_87_;
}
}
else
{
uint8_t v___x_88_; 
lean_dec_ref_known(v_x_75_, 1);
lean_dec_ref(v_x_76_);
lean_dec_ref(v_inst_74_);
v___x_88_ = 0;
return v___x_88_;
}
}
default: 
{
if (lean_obj_tag(v_x_76_) == 2)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_a_89_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v_x_75_, 1);
lean_inc_ref(v_a_90_);
lean_dec_ref_known(v_x_75_, 2);
v_a_91_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v_x_76_, 1);
lean_inc_ref(v_a_92_);
lean_dec_ref_known(v_x_76_, 2);
lean_inc_ref(v_inst_74_);
v___x_93_ = lean_apply_2(v_inst_74_, v_a_89_, v_a_91_);
v___x_94_ = lean_unbox(v___x_93_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
lean_dec_ref(v_a_92_);
lean_dec_ref(v_a_90_);
lean_dec_ref(v_inst_74_);
v___x_95_ = lean_unbox(v___x_93_);
return v___x_95_;
}
else
{
v_x_75_ = v_a_90_;
v_x_76_ = v_a_92_;
goto _start;
}
}
else
{
uint8_t v___x_97_; 
lean_dec_ref_known(v_x_75_, 2);
lean_dec_ref(v_x_76_);
lean_dec_ref(v_inst_74_);
v___x_97_ = 0;
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_99_, v_x_100_, v_x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___boxed(lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Lean_Widget_instBEqTaggedText_beq(v_00_u03b1_103_, v_inst_104_, v_x_105_, v_x_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText___redArg(lean_object* v_inst_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_110_, 0, lean_box(0));
lean_closure_set(v___x_110_, 1, v_inst_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText(lean_object* v_00_u03b1_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_113_, 0, lean_box(0));
lean_closure_set(v___x_113_, 1, v_inst_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_to_int(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(lean_object* v_inst_136_, lean_object* v_x_137_, lean_object* v_prec_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_136_, v_x_137_, v_prec_138_);
lean_dec(v_prec_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg(lean_object* v_inst_140_, lean_object* v_x_141_, lean_object* v_prec_142_){
_start:
{
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v_inst_140_);
v_a_143_ = lean_ctor_get(v_x_141_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_163_ == 0)
{
v___x_145_ = v_x_141_;
v_isShared_146_ = v_isSharedCheck_163_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v_x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_163_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___y_148_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1024u);
v___x_160_ = lean_nat_dec_le(v___x_159_, v_prec_142_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_148_ = v___x_161_;
goto v___jp_147_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_148_ = v___x_162_;
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_149_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2));
v___x_150_ = l_String_quote(v_a_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 3);
lean_ctor_set(v___x_145_, 0, v___x_150_);
v___x_152_ = v___x_145_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_158_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_149_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
lean_inc(v___y_148_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___y_148_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = 0;
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_155_);
v___x_157_ = l_Repr_addAppParen(v___x_156_, v_prec_142_);
return v___x_157_;
}
}
}
}
case 1:
{
lean_object* v_a_164_; lean_object* v_localinst_165_; lean_object* v___y_167_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_a_164_ = lean_ctor_get(v_x_141_, 0);
lean_inc_ref(v_a_164_);
lean_dec_ref_known(v_x_141_, 1);
v_localinst_165_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_165_, 0, v_inst_140_);
v___x_175_ = lean_unsigned_to_nat(1024u);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_prec_142_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_167_ = v___x_177_;
goto v___jp_166_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_167_ = v___x_178_;
goto v___jp_166_;
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_168_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7));
v___x_169_ = l_Array_repr___redArg(v_localinst_165_, v_a_164_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_inc(v___y_167_);
v___x_171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_171_, 0, v___y_167_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = 0;
v___x_173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v___x_172_);
v___x_174_ = l_Repr_addAppParen(v___x_173_, v_prec_142_);
return v___x_174_;
}
}
default: 
{
lean_object* v_a_179_; lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_203_; 
v_a_179_ = lean_ctor_get(v_x_141_, 0);
v_a_180_ = lean_ctor_get(v_x_141_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_203_ == 0)
{
v___x_182_ = v_x_141_;
v_isShared_183_ = v_isSharedCheck_203_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_inc(v_a_179_);
lean_dec(v_x_141_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_203_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___y_186_; uint8_t v___x_200_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_200_ = lean_nat_dec_le(v___x_184_, v_prec_142_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_186_ = v___x_201_;
goto v___jp_185_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_186_ = v___x_202_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_187_ = lean_box(1);
v___x_188_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10));
lean_inc_ref(v_inst_140_);
v___x_189_ = lean_apply_2(v_inst_140_, v_a_179_, v___x_184_);
if (v_isShared_183_ == 0)
{
lean_ctor_set_tag(v___x_182_, 5);
lean_ctor_set(v___x_182_, 1, v___x_189_);
lean_ctor_set(v___x_182_, 0, v___x_188_);
v___x_191_ = v___x_182_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_199_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_187_);
v___x_193_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_140_, v_a_180_, v___x_184_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
lean_inc(v___y_186_);
v___x_195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_186_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = l_Repr_addAppParen(v___x_197_, v_prec_142_);
return v___x_198_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr(lean_object* v_00_u03b1_204_, lean_object* v_inst_205_, lean_object* v_x_206_, lean_object* v_prec_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_205_, v_x_206_, v_prec_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___boxed(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_x_211_, lean_object* v_prec_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Widget_instReprTaggedText_repr(v_00_u03b1_209_, v_inst_210_, v_x_211_, v_prec_212_);
lean_dec(v_prec_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText___redArg(lean_object* v_inst_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_215_, 0, lean_box(0));
lean_closure_set(v___x_215_, 1, v_inst_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_218_, 0, lean_box(0));
lean_closure_set(v___x_218_, 1, v_inst_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(lean_object* v_inst_228_, lean_object* v_json_229_){
_start:
{
lean_object* v___x_230_; 
lean_inc(v_json_229_);
v___x_230_ = l_Lean_Json_getTag_x3f(v_json_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; 
lean_dec(v_json_229_);
lean_dec_ref(v_inst_228_);
v___x_231_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1));
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_349_; 
v_val_232_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_349_ == 0)
{
v___x_234_ = v___x_230_;
v_isShared_235_ = v_isSharedCheck_349_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v___x_230_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_349_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = lean_box(0);
v___x_237_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_238_ = lean_string_dec_eq(v_val_232_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
v___x_240_ = lean_string_dec_eq(v_val_232_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
lean_del_object(v___x_234_);
v___x_241_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
v___x_242_ = lean_string_dec_eq(v_val_232_, v___x_241_);
lean_dec(v_val_232_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v_json_229_);
lean_dec_ref(v_inst_228_);
v___x_243_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6));
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_unsigned_to_nat(2u);
v___x_245_ = lean_box(0);
v___x_246_ = l_Lean_Json_parseCtorFields(v_json_229_, v___x_241_, v___x_244_, v___x_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_inst_228_);
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_a_255_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_246_, 1);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_array_get_borrowed(v___x_236_, v_a_255_, v___x_256_);
lean_inc_ref(v_inst_228_);
lean_inc(v___x_257_);
v___x_258_ = lean_apply_1(v_inst_228_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_a_255_);
lean_dec_ref(v_inst_228_);
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_a_267_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_258_, 1);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_array_get(v___x_236_, v_a_255_, v___x_268_);
lean_dec(v_a_255_);
v___x_270_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_228_, v___x_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_dec(v_a_267_);
return v___x_270_;
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_279_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_275_, 0, v_a_267_);
lean_ctor_set(v___x_275_, 1, v_a_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_val_232_);
lean_dec_ref(v_inst_228_);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_box(0);
v___x_282_ = l_Lean_Json_parseCtorFields(v_json_229_, v___x_239_, v___x_280_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_del_object(v___x_234_);
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_a_291_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_282_, 1);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get(v___x_236_, v_a_291_, v___x_292_);
lean_dec(v_a_291_);
v___x_294_ = l_Lean_Json_getStr_x3f(v___x_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_del_object(v___x_234_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v_a_303_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_313_ == 0)
{
v___x_305_ = v___x_294_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_294_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set_tag(v___x_234_, 0);
lean_ctor_set(v___x_234_, 0, v_a_303_);
v___x_308_ = v___x_234_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_val_232_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_box(0);
v___x_316_ = l_Lean_Json_parseCtorFields(v_json_229_, v___x_237_, v___x_314_, v___x_315_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_del_object(v___x_234_);
lean_dec_ref(v_inst_228_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v_localinst_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_a_325_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_316_, 1);
v_localinst_326_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg), 2, 1);
lean_closure_set(v_localinst_326_, 0, v_inst_228_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get(v___x_236_, v_a_325_, v___x_327_);
lean_dec(v_a_325_);
v___x_329_ = l_Lean_Array_fromJson_x3f___redArg(v_localinst_326_, v___x_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_del_object(v___x_234_);
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v_a_338_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_348_ == 0)
{
v___x_340_ = v___x_329_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_329_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_a_338_);
v___x_343_ = v___x_234_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson(lean_object* v_00_u03b1_350_, lean_object* v_inst_351_, lean_object* v_json_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_351_, v_json_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText___redArg(lean_object* v_inst_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_355_, 0, lean_box(0));
lean_closure_set(v___x_355_, 1, v_inst_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_358_, 0, lean_box(0));
lean_closure_set(v___x_358_, 1, v_inst_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___redArg(lean_object* v_inst_359_, lean_object* v_x_360_){
_start:
{
switch(lean_obj_tag(v_x_360_))
{
case 0:
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_inst_359_);
v_a_361_ = lean_ctor_get(v_x_360_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_373_ == 0)
{
v___x_363_ = v_x_360_;
v_isShared_364_ = v_isSharedCheck_373_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v_x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_373_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 3);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_361_);
v___x_367_ = v_reuseFailAlloc_372_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_365_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_Lean_Json_mkObj(v___x_370_);
lean_dec_ref_known(v___x_370_, 2);
return v___x_371_;
}
}
}
case 1:
{
lean_object* v_a_374_; lean_object* v_localinst_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_374_ = lean_ctor_get(v_x_360_, 0);
lean_inc_ref(v_a_374_);
lean_dec_ref_known(v_x_360_, 1);
v_localinst_375_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson___redArg), 2, 1);
lean_closure_set(v_localinst_375_, 0, v_inst_359_);
v___x_376_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_377_ = l_Lean_Array_toJson___redArg(v_localinst_375_, v_a_374_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_Json_mkObj(v___x_380_);
lean_dec_ref_known(v___x_380_, 2);
return v___x_381_;
}
default: 
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_401_; 
v_a_382_ = lean_ctor_get(v_x_360_, 0);
v_a_383_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_401_ == 0)
{
v___x_385_ = v_x_360_;
v_isShared_386_ = v_isSharedCheck_401_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_inc(v_a_382_);
lean_dec(v_x_360_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_401_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_387_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
lean_inc_ref(v_inst_359_);
v___x_388_ = lean_apply_1(v_inst_359_, v_a_382_);
v___x_389_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_359_, v_a_383_);
v___x_390_ = lean_unsigned_to_nat(2u);
v___x_391_ = lean_mk_empty_array_with_capacity(v___x_390_);
v___x_392_ = lean_array_push(v___x_391_, v___x_388_);
v___x_393_ = lean_array_push(v___x_392_, v___x_389_);
v___x_394_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 0);
lean_ctor_set(v___x_385_, 1, v___x_394_);
lean_ctor_set(v___x_385_, 0, v___x_387_);
v___x_396_ = v___x_385_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_400_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_Json_mkObj(v___x_398_);
lean_dec_ref_known(v___x_398_, 2);
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson(lean_object* v_00_u03b1_402_, lean_object* v_inst_403_, lean_object* v_x_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_403_, v_x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText___redArg(lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_407_, 0, lean_box(0));
lean_closure_set(v___x_407_, 1, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText(lean_object* v_00_u03b1_408_, lean_object* v_inst_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_410_, 0, lean_box(0));
lean_closure_set(v___x_410_, 1, v_inst_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText___redArg(lean_object* v_s_u2080_411_, lean_object* v_x_412_){
_start:
{
switch(lean_obj_tag(v_x_412_))
{
case 0:
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_a_413_ = lean_ctor_get(v_x_412_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_x_412_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v_x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_string_append(v_a_413_, v_s_u2080_411_);
lean_dec_ref(v_s_u2080_411_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
case 1:
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_449_; 
v_a_422_ = lean_ctor_get(v_x_412_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_449_ == 0)
{
v___x_424_ = v_x_412_;
v_isShared_425_ = v_isSharedCheck_449_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v_x_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_449_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText___closed__0, &l_Lean_Widget_instInhabitedTaggedText___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText___closed__0);
v___x_427_ = lean_array_get_size(v_a_422_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_sub(v___x_427_, v___x_428_);
v___x_430_ = lean_array_get(v___x_426_, v_a_422_, v___x_429_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_443_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_443_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_string_append(v_a_431_, v_s_u2080_411_);
lean_dec_ref(v_s_u2080_411_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_442_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = lean_array_set(v_a_422_, v___x_429_, v___x_437_);
lean_dec(v___x_429_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_438_);
v___x_440_ = v___x_424_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_445_; 
lean_dec(v___x_430_);
lean_dec(v___x_429_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v_s_u2080_411_);
v___x_445_ = v___x_424_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_s_u2080_411_);
v___x_445_ = v_reuseFailAlloc_448_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_array_push(v_a_422_, v___x_445_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
}
}
default: 
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_s_u2080_411_);
v___x_451_ = lean_unsigned_to_nat(2u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_array_push(v___x_452_, v_x_412_);
v___x_454_ = lean_array_push(v___x_453_, v___x_450_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText(lean_object* v_00_u03b1_456_, lean_object* v_s_u2080_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_u2080_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag___redArg(lean_object* v_acc_460_, lean_object* v_t_u2080_461_, lean_object* v_a_u2080_462_){
_start:
{
lean_object* v_a_464_; 
switch(lean_obj_tag(v_acc_460_))
{
case 1:
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_480_; 
v_a_471_ = lean_ctor_get(v_acc_460_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_acc_460_);
if (v_isSharedCheck_480_ == 0)
{
v___x_473_ = v_acc_460_;
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v_acc_460_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v_t_u2080_461_);
lean_ctor_set(v___x_475_, 1, v_a_u2080_462_);
v___x_476_ = lean_array_push(v_a_471_, v___x_475_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_476_);
v___x_478_ = v___x_473_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
case 0:
{
lean_object* v_a_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_481_ = lean_ctor_get(v_acc_460_, 0);
v___x_482_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_483_ = lean_string_dec_eq(v_a_481_, v___x_482_);
if (v___x_483_ == 0)
{
v_a_464_ = v_acc_460_;
goto v___jp_463_;
}
else
{
lean_object* v___x_484_; 
lean_dec_ref_known(v_acc_460_, 1);
v___x_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_484_, 0, v_t_u2080_461_);
lean_ctor_set(v___x_484_, 1, v_a_u2080_462_);
return v___x_484_;
}
}
default: 
{
v_a_464_ = v_acc_460_;
goto v___jp_463_;
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v_t_u2080_461_);
lean_ctor_set(v___x_465_, 1, v_a_u2080_462_);
v___x_466_ = lean_unsigned_to_nat(2u);
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_466_);
v___x_468_ = lean_array_push(v___x_467_, v_a_464_);
v___x_469_ = lean_array_push(v___x_468_, v___x_465_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag(lean_object* v_00_u03b1_485_, lean_object* v_acc_486_, lean_object* v_t_u2080_487_, lean_object* v_a_u2080_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_acc_486_, v_t_u2080_487_, v_a_u2080_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(lean_object* v_f_490_, size_t v_sz_491_, size_t v_i_492_, lean_object* v_bs_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_494_ == 0)
{
lean_dec(v_f_490_);
return v_bs_493_;
}
else
{
lean_object* v_v_495_; lean_object* v___x_496_; lean_object* v_bs_x27_497_; lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v_v_495_ = lean_array_uget(v_bs_493_, v_i_492_);
v___x_496_ = lean_unsigned_to_nat(0u);
v_bs_x27_497_ = lean_array_uset(v_bs_493_, v_i_492_, v___x_496_);
lean_inc(v_f_490_);
v___x_498_ = l_Lean_Widget_TaggedText_map___redArg(v_f_490_, v_v_495_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_492_, v___x_499_);
v___x_501_ = lean_array_uset(v_bs_x27_497_, v_i_492_, v___x_498_);
v_i_492_ = v___x_500_;
v_bs_493_ = v___x_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map___redArg(lean_object* v_f_503_, lean_object* v_x_504_){
_start:
{
switch(lean_obj_tag(v_x_504_))
{
case 0:
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_f_503_);
v_a_505_ = lean_ctor_get(v_x_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v_x_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v_x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
case 1:
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_523_; 
v_a_513_ = lean_ctor_get(v_x_504_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_523_ == 0)
{
v___x_515_ = v_x_504_;
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_504_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_sz_517_ = lean_array_size(v_a_513_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_503_, v_sz_517_, v___x_518_, v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_519_);
v___x_521_ = v___x_515_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
default: 
{
lean_object* v_a_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_534_; 
v_a_524_ = lean_ctor_get(v_x_504_, 0);
v_a_525_ = lean_ctor_get(v_x_504_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_534_ == 0)
{
v___x_527_ = v_x_504_;
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_inc(v_a_524_);
lean_dec(v_x_504_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
lean_inc(v_f_503_);
v___x_529_ = lean_apply_1(v_f_503_, v_a_524_);
v___x_530_ = l_Lean_Widget_TaggedText_map___redArg(v_f_503_, v_a_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_530_);
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_532_ = v___x_527_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg___boxed(lean_object* v_f_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_535_, v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_f_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Widget_TaggedText_map___redArg(v_f_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, lean_object* v_f_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_bs_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_549_, v_sz_550_, v_i_551_, v_bs_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_f_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_bs_559_){
_start:
{
size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v_sz_boxed_560_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_561_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(v_00_u03b1_554_, v_00_u03b2_555_, v_f_556_, v_sz_boxed_560_, v_i_boxed_561_, v_bs_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__0(lean_object* v_toPure_563_, lean_object* v_____do__lift_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_____do__lift_564_);
v___x_566_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__1(lean_object* v_____do__lift_567_, lean_object* v_toPure_568_, lean_object* v_____do__lift_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v_____do__lift_567_);
lean_ctor_set(v___x_570_, 1, v_____do__lift_569_);
v___x_571_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object* v_inst_572_, lean_object* v_f_573_, lean_object* v_x_574_){
_start:
{
switch(lean_obj_tag(v_x_574_))
{
case 0:
{
lean_object* v_toApplicative_575_; lean_object* v_toPure_576_; lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_585_; 
v_toApplicative_575_ = lean_ctor_get(v_inst_572_, 0);
lean_inc_ref(v_toApplicative_575_);
lean_dec(v_f_573_);
lean_dec_ref(v_inst_572_);
v_toPure_576_ = lean_ctor_get(v_toApplicative_575_, 1);
lean_inc(v_toPure_576_);
lean_dec_ref(v_toApplicative_575_);
v_a_577_ = lean_ctor_get(v_x_574_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_585_ == 0)
{
v___x_579_ = v_x_574_;
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v_x_574_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_584_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; 
v___x_583_ = lean_apply_2(v_toPure_576_, lean_box(0), v___x_582_);
return v___x_583_;
}
}
}
case 1:
{
lean_object* v_toApplicative_586_; lean_object* v_toBind_587_; lean_object* v_toPure_588_; lean_object* v_a_589_; lean_object* v___f_590_; lean_object* v___x_591_; size_t v_sz_592_; size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_toApplicative_586_ = lean_ctor_get(v_inst_572_, 0);
v_toBind_587_ = lean_ctor_get(v_inst_572_, 1);
lean_inc(v_toBind_587_);
v_toPure_588_ = lean_ctor_get(v_toApplicative_586_, 1);
v_a_589_ = lean_ctor_get(v_x_574_, 0);
lean_inc_ref(v_a_589_);
lean_dec_ref_known(v_x_574_, 1);
lean_inc(v_toPure_588_);
v___f_590_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_590_, 0, v_toPure_588_);
lean_inc_ref(v_inst_572_);
v___x_591_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg), 3, 2);
lean_closure_set(v___x_591_, 0, v_inst_572_);
lean_closure_set(v___x_591_, 1, v_f_573_);
v_sz_592_ = lean_array_size(v_a_589_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_572_, v___x_591_, v_sz_592_, v___x_593_, v_a_589_);
v___x_595_ = lean_apply_4(v_toBind_587_, lean_box(0), lean_box(0), v___x_594_, v___f_590_);
return v___x_595_;
}
default: 
{
lean_object* v_toApplicative_596_; lean_object* v_toBind_597_; lean_object* v_toPure_598_; lean_object* v_a_599_; lean_object* v_a_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_toApplicative_596_ = lean_ctor_get(v_inst_572_, 0);
v_toBind_597_ = lean_ctor_get(v_inst_572_, 1);
lean_inc_n(v_toBind_597_, 2);
v_toPure_598_ = lean_ctor_get(v_toApplicative_596_, 1);
lean_inc(v_toPure_598_);
v_a_599_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_599_);
v_a_600_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_a_600_);
lean_dec_ref_known(v_x_574_, 2);
lean_inc(v_f_573_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_601_, 0, v_toPure_598_);
lean_closure_set(v___f_601_, 1, v_inst_572_);
lean_closure_set(v___f_601_, 2, v_f_573_);
lean_closure_set(v___f_601_, 3, v_a_600_);
lean_closure_set(v___f_601_, 4, v_toBind_597_);
v___x_602_ = lean_apply_1(v_f_573_, v_a_599_);
v___x_603_ = lean_apply_4(v_toBind_597_, lean_box(0), lean_box(0), v___x_602_, v___f_601_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__2(lean_object* v_toPure_604_, lean_object* v_inst_605_, lean_object* v_f_606_, lean_object* v_a_607_, lean_object* v_toBind_608_, lean_object* v_____do__lift_609_){
_start:
{
lean_object* v___f_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___f_610_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_610_, 0, v_____do__lift_609_);
lean_closure_set(v___f_610_, 1, v_toPure_604_);
v___x_611_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_605_, v_f_606_, v_a_607_);
v___x_612_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_611_, v___f_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM(lean_object* v_m_613_, lean_object* v_00_u03b1_614_, lean_object* v_00_u03b2_615_, lean_object* v_inst_616_, lean_object* v_f_617_, lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_616_, v_f_617_, v_x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__1(lean_object* v_inst_620_, lean_object* v_f_621_, lean_object* v_a_622_, lean_object* v_____r_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_620_, v_f_621_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg(lean_object* v_inst_625_, lean_object* v_f_626_, lean_object* v_x_627_){
_start:
{
switch(lean_obj_tag(v_x_627_))
{
case 0:
{
lean_object* v_toApplicative_628_; lean_object* v_toPure_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_toApplicative_628_ = lean_ctor_get(v_inst_625_, 0);
lean_inc_ref(v_toApplicative_628_);
lean_dec_ref_known(v_x_627_, 1);
lean_dec(v_f_626_);
lean_dec_ref(v_inst_625_);
v_toPure_629_ = lean_ctor_get(v_toApplicative_628_, 1);
lean_inc(v_toPure_629_);
lean_dec_ref(v_toApplicative_628_);
v___x_630_ = lean_box(0);
v___x_631_ = lean_apply_2(v_toPure_629_, lean_box(0), v___x_630_);
return v___x_631_;
}
case 1:
{
lean_object* v_toApplicative_632_; lean_object* v_toPure_633_; lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_toApplicative_632_ = lean_ctor_get(v_inst_625_, 0);
v_toPure_633_ = lean_ctor_get(v_toApplicative_632_, 1);
v_a_634_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_a_634_);
lean_dec_ref_known(v_x_627_, 1);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_array_get_size(v_a_634_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_inc(v_toPure_633_);
lean_dec_ref(v_a_634_);
lean_dec(v_f_626_);
lean_dec_ref(v_inst_625_);
v___x_639_ = lean_apply_2(v_toPure_633_, lean_box(0), v___x_637_);
return v___x_639_;
}
else
{
lean_object* v___f_640_; uint8_t v___x_641_; 
lean_inc_ref(v_inst_625_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_640_, 0, v_inst_625_);
lean_closure_set(v___f_640_, 1, v_f_626_);
v___x_641_ = lean_nat_dec_le(v___x_636_, v___x_636_);
if (v___x_641_ == 0)
{
if (v___x_638_ == 0)
{
lean_object* v___x_642_; 
lean_inc(v_toPure_633_);
lean_dec_ref(v___f_640_);
lean_dec_ref(v_a_634_);
lean_dec_ref(v_inst_625_);
v___x_642_ = lean_apply_2(v_toPure_633_, lean_box(0), v___x_637_);
return v___x_642_;
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_636_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_625_, v___f_640_, v_a_634_, v___x_643_, v___x_644_, v___x_637_);
return v___x_645_;
}
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_636_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_625_, v___f_640_, v_a_634_, v___x_646_, v___x_647_, v___x_637_);
return v___x_648_;
}
}
}
default: 
{
lean_object* v_toBind_649_; lean_object* v_a_650_; lean_object* v_a_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_toBind_649_ = lean_ctor_get(v_inst_625_, 1);
lean_inc(v_toBind_649_);
v_a_650_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_a_650_);
v_a_651_ = lean_ctor_get(v_x_627_, 1);
lean_inc_ref_n(v_a_651_, 2);
lean_dec_ref_known(v_x_627_, 2);
lean_inc(v_f_626_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_652_, 0, v_inst_625_);
lean_closure_set(v___f_652_, 1, v_f_626_);
lean_closure_set(v___f_652_, 2, v_a_651_);
v___x_653_ = lean_apply_2(v_f_626_, v_a_650_, v_a_651_);
v___x_654_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_653_, v___f_652_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__0(lean_object* v_inst_655_, lean_object* v_f_656_, lean_object* v_x_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_655_, v_f_656_, v___y_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM(lean_object* v_m_660_, lean_object* v_00_u03b1_661_, lean_object* v_inst_662_, lean_object* v_f_663_, lean_object* v_x_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_662_, v_f_663_, v_x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(lean_object* v_f_666_, size_t v_sz_667_, size_t v_i_668_, lean_object* v_bs_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_lt(v_i_668_, v_sz_667_);
if (v___x_670_ == 0)
{
lean_dec_ref(v_f_666_);
return v_bs_669_;
}
else
{
lean_object* v_v_671_; lean_object* v___x_672_; lean_object* v_bs_x27_673_; lean_object* v___x_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v_v_671_ = lean_array_uget(v_bs_669_, v_i_668_);
v___x_672_ = lean_unsigned_to_nat(0u);
v_bs_x27_673_ = lean_array_uset(v_bs_669_, v_i_668_, v___x_672_);
lean_inc_ref(v_f_666_);
v___x_674_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_666_, v_v_671_);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_668_, v___x_675_);
v___x_677_ = lean_array_uset(v_bs_x27_673_, v_i_668_, v___x_674_);
v_i_668_ = v___x_676_;
v_bs_669_ = v___x_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object* v_f_679_, lean_object* v_x_680_){
_start:
{
switch(lean_obj_tag(v_x_680_))
{
case 0:
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_f_679_);
v_a_681_ = lean_ctor_get(v_x_680_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v_x_680_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v_x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
case 1:
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v_a_689_ = lean_ctor_get(v_x_680_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_699_ == 0)
{
v___x_691_ = v_x_680_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v_x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
size_t v_sz_693_; size_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v_sz_693_ = lean_array_size(v_a_689_);
v___x_694_ = ((size_t)0ULL);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_679_, v_sz_693_, v___x_694_, v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_695_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
default: 
{
lean_object* v_a_700_; lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_700_ = lean_ctor_get(v_x_680_, 0);
lean_inc(v_a_700_);
v_a_701_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_a_701_);
lean_dec_ref_known(v_x_680_, 2);
v___x_702_ = lean_apply_2(v_f_679_, v_a_700_, v_a_701_);
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg___boxed(lean_object* v_f_703_, lean_object* v_sz_704_, lean_object* v_i_705_, lean_object* v_bs_706_){
_start:
{
size_t v_sz_boxed_707_; size_t v_i_boxed_708_; lean_object* v_res_709_; 
v_sz_boxed_707_ = lean_unbox_usize(v_sz_704_);
lean_dec(v_sz_704_);
v_i_boxed_708_ = lean_unbox_usize(v_i_705_);
lean_dec(v_i_705_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_703_, v_sz_boxed_707_, v_i_boxed_708_, v_bs_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite(lean_object* v_00_u03b1_710_, lean_object* v_00_u03b2_711_, lean_object* v_f_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_f_717_, size_t v_sz_718_, size_t v_i_719_, lean_object* v_bs_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_717_, v_sz_718_, v_i_719_, v_bs_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_f_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_bs_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(v_00_u03b1_722_, v_00_u03b2_723_, v_f_724_, v_sz_boxed_728_, v_i_boxed_729_, v_bs_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___redArg(lean_object* v_inst_731_, lean_object* v_f_732_, lean_object* v_x_733_){
_start:
{
switch(lean_obj_tag(v_x_733_))
{
case 0:
{
lean_object* v_toApplicative_734_; lean_object* v_toPure_735_; lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_toApplicative_734_ = lean_ctor_get(v_inst_731_, 0);
lean_inc_ref(v_toApplicative_734_);
lean_dec(v_f_732_);
lean_dec_ref(v_inst_731_);
v_toPure_735_ = lean_ctor_get(v_toApplicative_734_, 1);
lean_inc(v_toPure_735_);
lean_dec_ref(v_toApplicative_734_);
v_a_736_ = lean_ctor_get(v_x_733_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v_x_733_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v_x_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_apply_2(v_toPure_735_, lean_box(0), v___x_741_);
return v___x_742_;
}
}
}
case 1:
{
lean_object* v_toApplicative_745_; lean_object* v_toBind_746_; lean_object* v_toPure_747_; lean_object* v_a_748_; lean_object* v___f_749_; lean_object* v___x_750_; size_t v_sz_751_; size_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_toApplicative_745_ = lean_ctor_get(v_inst_731_, 0);
v_toBind_746_ = lean_ctor_get(v_inst_731_, 1);
lean_inc(v_toBind_746_);
v_toPure_747_ = lean_ctor_get(v_toApplicative_745_, 1);
v_a_748_ = lean_ctor_get(v_x_733_, 0);
lean_inc_ref(v_a_748_);
lean_dec_ref_known(v_x_733_, 1);
lean_inc(v_toPure_747_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_749_, 0, v_toPure_747_);
lean_inc_ref(v_inst_731_);
v___x_750_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_rewriteM___redArg), 3, 2);
lean_closure_set(v___x_750_, 0, v_inst_731_);
lean_closure_set(v___x_750_, 1, v_f_732_);
v_sz_751_ = lean_array_size(v_a_748_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_731_, v___x_750_, v_sz_751_, v___x_752_, v_a_748_);
v___x_754_ = lean_apply_4(v_toBind_746_, lean_box(0), lean_box(0), v___x_753_, v___f_749_);
return v___x_754_;
}
default: 
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_757_; 
lean_dec_ref(v_inst_731_);
v_a_755_ = lean_ctor_get(v_x_733_, 0);
lean_inc(v_a_755_);
v_a_756_ = lean_ctor_get(v_x_733_, 1);
lean_inc_ref(v_a_756_);
lean_dec_ref_known(v_x_733_, 2);
v___x_757_ = lean_apply_2(v_f_732_, v_a_755_, v_a_756_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM(lean_object* v_m_758_, lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_inst_761_, lean_object* v_f_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Widget_TaggedText_rewriteM___redArg(v_inst_761_, v_f_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(lean_object* v_inst_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v_a_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_rpcEncode_770_; lean_object* v___x_641__overap_771_; lean_object* v___x_772_; lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_rpcEncode_770_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_rpcEncode_770_);
lean_dec_ref(v_inst_765_);
v___x_641__overap_771_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_766_, v_rpcEncode_770_, v_a_768_);
v___x_772_ = lean_apply_1(v___x_641__overap_771_, v___y_769_);
v_fst_773_ = lean_ctor_get(v___x_772_, 0);
v_snd_774_ = lean_ctor_get(v___x_772_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_772_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_snd_774_);
lean_inc(v_fst_773_);
lean_dec(v___x_772_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v___x_767_, v_fst_773_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_snd_774_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(lean_object* v___f_783_, lean_object* v_inst_784_, lean_object* v___x_785_, lean_object* v_a_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v___f_783_, v_a_786_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_inst_784_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v_rpcDecode_798_; lean_object* v___x_654__overap_799_; lean_object* v___x_800_; 
v_a_797_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_788_, 1);
v_rpcDecode_798_ = lean_ctor_get(v_inst_784_, 1);
lean_inc_ref(v_rpcDecode_798_);
lean_dec_ref(v_inst_784_);
v___x_654__overap_799_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_785_, v_rpcDecode_798_, v_a_797_);
lean_inc_ref(v___y_787_);
v___x_800_ = lean_apply_1(v___x_654__overap_799_, v___y_787_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed(lean_object* v___f_801_, lean_object* v_inst_802_, lean_object* v___x_803_, lean_object* v_a_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(v___f_801_, v_inst_802_, v___x_803_, v_a_804_, v___y_805_);
lean_dec_ref(v___y_805_);
return v_res_806_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9));
v___x_854_ = l_ReaderT_instMonad___redArg(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22(void){
_start:
{
lean_object* v___x_855_; lean_object* v___f_856_; 
v___x_855_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_856_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_856_, 0, v___x_855_);
return v___f_856_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23(void){
_start:
{
lean_object* v___x_857_; lean_object* v___f_858_; 
v___x_857_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_858_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_858_, 0, v___x_857_);
return v___f_858_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24(void){
_start:
{
lean_object* v___x_859_; lean_object* v___f_860_; 
v___x_859_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_860_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_860_, 0, v___x_859_);
return v___f_860_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25(void){
_start:
{
lean_object* v___x_861_; lean_object* v___f_862_; 
v___x_861_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_862_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_862_, 0, v___x_861_);
return v___f_862_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_864_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_864_, 0, lean_box(0));
lean_closure_set(v___x_864_, 1, lean_box(0));
lean_closure_set(v___x_864_, 2, v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27(void){
_start:
{
lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___f_865_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22);
v___x_866_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___f_865_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_869_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_869_, 0, lean_box(0));
lean_closure_set(v___x_869_, 1, lean_box(0));
lean_closure_set(v___x_869_, 2, v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29(void){
_start:
{
lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___f_870_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25);
v___f_871_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24);
v___f_872_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23);
v___x_873_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28);
v___x_874_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27);
v___x_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
lean_ctor_set(v___x_875_, 2, v___f_872_);
lean_ctor_set(v___x_875_, 3, v___f_871_);
lean_ctor_set(v___x_875_, 4, v___f_870_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_877_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_877_, 0, lean_box(0));
lean_closure_set(v___x_877_, 1, lean_box(0));
lean_closure_set(v___x_877_, 2, v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30);
v___x_879_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg(lean_object* v_inst_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; 
v___x_883_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_884_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20));
lean_inc_ref(v_inst_882_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0), 5, 3);
lean_closure_set(v___f_885_, 0, v_inst_882_);
lean_closure_set(v___f_885_, 1, v___x_883_);
lean_closure_set(v___f_885_, 2, v___x_884_);
v___x_886_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31);
v___f_887_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32));
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_888_, 0, v___f_887_);
lean_closure_set(v___f_888_, 1, v_inst_882_);
lean_closure_set(v___f_888_, 2, v___x_886_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___f_885_);
lean_ctor_set(v___x_889_, 1, v___f_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable(lean_object* v_00_u03b1_890_, lean_object* v_inst_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object* v_s_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_out_903_; lean_object* v_tagStack_904_; lean_object* v_column_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_917_; 
v_out_903_ = lean_ctor_get(v___y_902_, 0);
v_tagStack_904_ = lean_ctor_get(v___y_902_, 1);
v_column_905_ = lean_ctor_get(v___y_902_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v___y_902_);
if (v_isSharedCheck_917_ == 0)
{
v___x_907_ = v___y_902_;
v_isShared_908_ = v_isSharedCheck_917_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_column_905_);
lean_inc(v_tagStack_904_);
lean_inc(v_out_903_);
lean_dec(v___y_902_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_917_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_909_ = lean_box(0);
lean_inc_ref(v_s_901_);
v___x_910_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_901_, v_out_903_);
v___x_911_ = lean_string_length(v_s_901_);
lean_dec_ref(v_s_901_);
v___x_912_ = lean_nat_add(v_column_905_, v___x_911_);
lean_dec(v_column_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 2, v___x_912_);
lean_ctor_set(v___x_907_, 0, v___x_910_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_tagStack_904_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v___x_912_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_909_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t v___x_918_, lean_object* v_s_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_string_push(v_s_919_, v___x_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object* v___x_921_, lean_object* v_s_922_){
_start:
{
uint32_t v___x_827__boxed_923_; lean_object* v_res_924_; 
v___x_827__boxed_923_ = lean_unbox_uint32(v___x_921_);
lean_dec(v___x_921_);
v_res_924_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_827__boxed_923_, v_s_922_);
return v_res_924_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_926_; lean_object* v___x_927_; 
v___x_926_ = 32;
v___x_927_ = lean_box_uint32(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___f_929_; 
v___x_928_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
v___f_929_ = lean_alloc_closure((void*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed), 2, 1);
lean_closure_set(v___f_929_, 0, v___x_928_);
return v___f_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object* v_indent_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_out_932_; lean_object* v_tagStack_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_946_; 
v_out_932_ = lean_ctor_get(v___y_931_, 0);
v_tagStack_933_ = lean_ctor_get(v___y_931_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v___y_931_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___y_931_, 2);
lean_dec(v_unused_947_);
v___x_935_ = v___y_931_;
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_tagStack_933_);
lean_inc(v_out_932_);
lean_dec(v___y_931_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_937_ = lean_box(0);
v___x_938_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
v___f_939_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
lean_inc(v_indent_930_);
v___x_940_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_939_, v_indent_930_, v___x_938_);
v___x_941_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_940_, v_out_932_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 2, v_indent_930_);
lean_ctor_set(v___x_935_, 0, v___x_941_);
v___x_943_ = v___x_935_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_tagStack_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_indent_930_);
v___x_943_ = v_reuseFailAlloc_945_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_937_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object* v_____do__lift_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_column_950_; lean_object* v___x_951_; 
v_column_950_ = lean_ctor_get(v_____do__lift_948_, 2);
lean_inc(v_column_950_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_column_950_);
lean_ctor_set(v___x_951_, 1, v___y_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object* v_____do__lift_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_952_, v___y_953_);
lean_dec_ref(v_____do__lift_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object* v_n_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_out_957_; lean_object* v_tagStack_958_; lean_object* v_column_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_972_; 
v_out_957_ = lean_ctor_get(v___y_956_, 0);
v_tagStack_958_ = lean_ctor_get(v___y_956_, 1);
v_column_959_ = lean_ctor_get(v___y_956_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v___y_956_);
if (v_isSharedCheck_972_ == 0)
{
v___x_961_ = v___y_956_;
v_isShared_962_ = v_isSharedCheck_972_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_column_959_);
lean_inc(v_tagStack_958_);
lean_inc(v_out_957_);
lean_dec(v___y_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_972_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_963_ = lean_box(0);
v___x_964_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_959_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_column_959_);
lean_ctor_set(v___x_965_, 1, v_out_957_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_n_955_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_tagStack_958_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_967_);
lean_ctor_set(v___x_961_, 0, v___x_964_);
v___x_969_ = v___x_961_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_column_959_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_963_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object* v_acc_973_, lean_object* v_x_974_){
_start:
{
lean_object* v_snd_975_; lean_object* v_fst_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_snd_975_ = lean_ctor_get(v_x_974_, 1);
lean_inc(v_snd_975_);
v_fst_976_ = lean_ctor_get(v_x_974_, 0);
lean_inc(v_fst_976_);
lean_dec_ref(v_x_974_);
v_fst_977_ = lean_ctor_get(v_snd_975_, 0);
v_snd_978_ = lean_ctor_get(v_snd_975_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_snd_975_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v_snd_975_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v_snd_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_fst_977_);
lean_ctor_set(v___x_980_, 0, v_fst_976_);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_fst_977_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_978_, v___x_983_, v_acc_973_);
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object* v___f_989_, lean_object* v_n_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_out_992_; lean_object* v_tagStack_993_; lean_object* v_column_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1007_; 
v_out_992_ = lean_ctor_get(v___y_991_, 0);
v_tagStack_993_ = lean_ctor_get(v___y_991_, 1);
v_column_994_ = lean_ctor_get(v___y_991_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___y_991_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_996_ = v___y_991_;
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_column_994_);
lean_inc(v_tagStack_993_);
lean_inc(v_out_992_);
lean_dec(v___y_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_out_x27_1002_; lean_object* v___x_1004_; 
v___x_998_ = lean_box(0);
v___x_999_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_n_990_);
lean_inc(v_tagStack_993_);
v___x_1000_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_993_, v_tagStack_993_, v_n_990_, v___x_999_);
v___x_1001_ = l_List_drop___redArg(v_n_990_, v_tagStack_993_);
lean_dec(v_tagStack_993_);
v_out_x27_1002_ = l_List_foldl___redArg(v___f_989_, v_out_992_, v___x_1000_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___x_1001_);
lean_ctor_set(v___x_996_, 0, v_out_x27_1002_);
v___x_1004_ = v___x_996_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_out_x27_1002_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_column_994_);
v___x_1004_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_998_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_zero_1030_; uint8_t v_isZero_1031_; 
v_zero_1030_ = lean_unsigned_to_nat(0u);
v_isZero_1031_ = lean_nat_dec_eq(v_x_1028_, v_zero_1030_);
if (v_isZero_1031_ == 1)
{
lean_dec(v_x_1028_);
return v_x_1029_;
}
else
{
uint32_t v___x_1032_; lean_object* v_one_1033_; lean_object* v_n_1034_; lean_object* v___x_1035_; 
v___x_1032_ = 32;
v_one_1033_ = lean_unsigned_to_nat(1u);
v_n_1034_ = lean_nat_sub(v_x_1028_, v_one_1033_);
lean_dec(v_x_1028_);
v___x_1035_ = lean_string_push(v_x_1029_, v___x_1032_);
v_x_1028_ = v_n_1034_;
v_x_1029_ = v___x_1035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object* v_fla_1037_, uint8_t v_flb_1038_, lean_object* v_tail_1039_, lean_object* v_is_x27_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1041_, 0, v_fla_1037_);
lean_ctor_set(v___x_1041_, 1, v_is_x27_1040_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*2, v_flb_1038_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_tail_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object* v_fla_1043_, lean_object* v_flb_1044_, lean_object* v_tail_1045_, lean_object* v_is_x27_1046_){
_start:
{
uint8_t v_flb_6217__boxed_1047_; lean_object* v_res_1048_; 
v_flb_6217__boxed_1047_ = lean_unbox(v_flb_1044_);
v_res_1048_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1043_, v_flb_6217__boxed_1047_, v_tail_1045_, v_is_x27_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t v_flb_1049_, lean_object* v_items_1050_, lean_object* v_gs_1051_, lean_object* v_w_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___y_1055_; lean_object* v_column_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v_g_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_r_1068_; lean_object* v___y_1070_; uint8_t v_foundLine_1075_; lean_object* v_space_1076_; uint8_t v___x_1077_; 
v_column_1060_ = lean_ctor_get(v___y_1053_, 2);
v___x_1061_ = 0;
v___x_1062_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1049_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1063_, 0, v___x_1062_);
lean_inc(v_items_1050_);
v_g_1064_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1064_, 0, v___x_1063_);
lean_ctor_set(v_g_1064_, 1, v_items_1050_);
lean_ctor_set_uint8(v_g_1064_, sizeof(void*)*2, v_flb_1049_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_g_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_nat_sub(v_w_1052_, v_column_1060_);
lean_inc(v___x_1067_);
lean_inc(v_column_1060_);
v_r_1068_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1066_, v_column_1060_, v___x_1067_);
v_foundLine_1075_ = lean_ctor_get_uint8(v_r_1068_, sizeof(void*)*1);
v_space_1076_ = lean_ctor_get(v_r_1068_, 0);
lean_inc(v_space_1076_);
v___x_1077_ = lean_nat_dec_lt(v___x_1067_, v_space_1076_);
if (v___x_1077_ == 0)
{
if (v_foundLine_1075_ == 0)
{
lean_object* v___x_1078_; lean_object* v_r_u2082_1079_; uint8_t v_foundLine_1080_; uint8_t v_foundFlattenedHardLine_1081_; lean_object* v_space_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v___x_1078_ = lean_nat_sub(v___x_1067_, v_space_1076_);
lean_inc(v_column_1060_);
lean_inc(v_gs_1051_);
v_r_u2082_1079_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1051_, v_column_1060_, v___x_1078_);
v_foundLine_1080_ = lean_ctor_get_uint8(v_r_u2082_1079_, sizeof(void*)*1);
v_foundFlattenedHardLine_1081_ = lean_ctor_get_uint8(v_r_u2082_1079_, sizeof(void*)*1 + 1);
v_space_1082_ = lean_ctor_get(v_r_u2082_1079_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_r_u2082_1079_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1084_ = v_r_u2082_1079_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_space_1082_);
lean_dec(v_r_u2082_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_nat_add(v_space_1076_, v_space_1082_);
lean_dec(v_space_1082_);
lean_dec(v_space_1076_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1089_, sizeof(void*)*1, v_foundLine_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1089_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1081_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v___y_1070_ = v___x_1088_;
goto v___jp_1069_;
}
}
}
else
{
lean_dec(v_space_1076_);
lean_inc_ref(v_r_1068_);
v___y_1070_ = v_r_1068_;
goto v___jp_1069_;
}
}
else
{
lean_dec(v_space_1076_);
lean_inc_ref(v_r_1068_);
v___y_1070_ = v_r_1068_;
goto v___jp_1069_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1056_, 0, v___y_1055_);
v___x_1057_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_items_1050_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*2, v_flb_1049_);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_gs_1051_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___y_1053_);
return v___x_1059_;
}
v___jp_1069_:
{
uint8_t v_foundFlattenedHardLine_1071_; 
v_foundFlattenedHardLine_1071_ = lean_ctor_get_uint8(v_r_1068_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1068_);
if (v_foundFlattenedHardLine_1071_ == 0)
{
lean_object* v_space_1072_; uint8_t v___x_1073_; 
v_space_1072_ = lean_ctor_get(v___y_1070_, 0);
lean_inc(v_space_1072_);
lean_dec_ref(v___y_1070_);
v___x_1073_ = lean_nat_dec_le(v_space_1072_, v___x_1067_);
lean_dec(v___x_1067_);
lean_dec(v_space_1072_);
v___y_1055_ = v___x_1073_;
goto v___jp_1054_;
}
else
{
uint8_t v___x_1074_; 
lean_dec_ref(v___y_1070_);
lean_dec(v___x_1067_);
v___x_1074_ = 0;
v___y_1055_ = v___x_1074_;
goto v___jp_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object* v_flb_1091_, lean_object* v_items_1092_, lean_object* v_gs_1093_, lean_object* v_w_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v_flb_boxed_1096_; lean_object* v_res_1097_; 
v_flb_boxed_1096_ = lean_unbox(v_flb_1091_);
v_res_1097_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_1096_, v_items_1092_, v_gs_1093_, v_w_1094_, v___y_1095_);
lean_dec(v_w_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 0)
{
return v_x_1098_;
}
else
{
lean_object* v_head_1100_; lean_object* v_snd_1101_; lean_object* v_tail_1102_; lean_object* v_fst_1103_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
v_head_1100_ = lean_ctor_get(v_x_1099_, 0);
lean_inc(v_head_1100_);
v_snd_1101_ = lean_ctor_get(v_head_1100_, 1);
lean_inc(v_snd_1101_);
v_tail_1102_ = lean_ctor_get(v_x_1099_, 1);
lean_inc(v_tail_1102_);
lean_dec_ref_known(v_x_1099_, 2);
v_fst_1103_ = lean_ctor_get(v_head_1100_, 0);
lean_inc(v_fst_1103_);
lean_dec(v_head_1100_);
v_fst_1104_ = lean_ctor_get(v_snd_1101_, 0);
v_snd_1105_ = lean_ctor_get(v_snd_1101_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_snd_1101_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v_snd_1101_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_snd_1105_);
lean_inc(v_fst_1104_);
lean_dec(v_snd_1101_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v_fst_1104_);
lean_ctor_set(v___x_1107_, 0, v_fst_1103_);
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_fst_1103_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_fst_1104_);
v___x_1110_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_1105_, v___x_1110_, v_x_1098_);
v_x_1098_ = v___x_1111_;
v_x_1099_ = v_tail_1102_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_1117_ = l_instInhabitedOfMonad___redArg(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object* v_msg_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_6144__overap_1121_; lean_object* v___x_1122_; 
v___x_1120_ = lean_obj_once(&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0, &l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once, _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
v___x_6144__overap_1121_ = lean_panic_fn_borrowed(v___x_1120_, v_msg_1118_);
v___x_1122_ = lean_apply_1(v___x_6144__overap_1121_, v___y_1119_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1125_ = lean_string_length(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object* v_w_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___y_1129_);
return v___x_1131_;
}
else
{
lean_object* v_head_1132_; lean_object* v_items_1133_; 
v_head_1132_ = lean_ctor_get(v_x_1128_, 0);
v_items_1133_ = lean_ctor_get(v_head_1132_, 1);
lean_inc(v_items_1133_);
if (lean_obj_tag(v_items_1133_) == 0)
{
lean_object* v_tail_1134_; 
v_tail_1134_ = lean_ctor_get(v_x_1128_, 1);
lean_inc(v_tail_1134_);
lean_dec_ref_known(v_x_1128_, 2);
v_x_1128_ = v_tail_1134_;
goto _start;
}
else
{
lean_object* v_head_1136_; lean_object* v_tail_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1488_; 
lean_inc(v_head_1132_);
v_head_1136_ = lean_ctor_get(v_items_1133_, 0);
lean_inc(v_head_1136_);
v_tail_1137_ = lean_ctor_get(v_x_1128_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_x_1128_, 0);
lean_dec(v_unused_1489_);
v___x_1139_ = v_x_1128_;
v_isShared_1140_ = v_isSharedCheck_1488_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_tail_1137_);
lean_dec(v_x_1128_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1488_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_fla_1141_; uint8_t v_flb_1142_; lean_object* v_tail_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1486_; 
v_fla_1141_ = lean_ctor_get(v_head_1132_, 0);
lean_inc(v_fla_1141_);
v_flb_1142_ = lean_ctor_get_uint8(v_head_1132_, sizeof(void*)*2);
lean_dec(v_head_1132_);
v_tail_1143_ = lean_ctor_get(v_items_1133_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_items_1133_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_items_1133_, 0);
lean_dec(v_unused_1487_);
v___x_1145_ = v_items_1133_;
v_isShared_1146_ = v_isSharedCheck_1486_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_tail_1143_);
lean_dec(v_items_1133_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1486_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_f_1147_; lean_object* v_indent_1148_; lean_object* v_activeTags_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1485_; 
v_f_1147_ = lean_ctor_get(v_head_1136_, 0);
v_indent_1148_ = lean_ctor_get(v_head_1136_, 1);
v_activeTags_1149_ = lean_ctor_get(v_head_1136_, 2);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_head_1136_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1151_ = v_head_1136_;
v_isShared_1152_ = v_isSharedCheck_1485_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_activeTags_1149_);
lean_inc(v_indent_1148_);
lean_inc(v_f_1147_);
lean_dec(v_head_1136_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1485_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___y_1194_; 
switch(lean_obj_tag(v_f_1147_))
{
case 0:
{
lean_object* v_out_1211_; lean_object* v_tagStack_1212_; lean_object* v_column_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1151_);
lean_dec(v_indent_1148_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1139_);
v_out_1211_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1212_ = lean_ctor_get(v___y_1129_, 1);
v_column_1213_ = lean_ctor_get(v___y_1129_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1215_ = v___y_1129_;
v_isShared_1216_ = v_isSharedCheck_1226_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_column_1213_);
lean_inc(v_tagStack_1212_);
lean_inc(v_out_1211_);
lean_dec(v___y_1129_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1226_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_out_x27_1220_; lean_object* v___x_1222_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1212_);
v___x_1218_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1212_, v_tagStack_1212_, v_activeTags_1149_, v___x_1217_);
v___x_1219_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1212_);
lean_dec(v_tagStack_1212_);
v_out_x27_1220_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1211_, v___x_1218_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1219_);
lean_ctor_set(v___x_1215_, 0, v_out_x27_1220_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_out_x27_1220_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_column_1213_);
v___x_1222_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1223_;
v___y_1129_ = v___x_1222_;
goto _start;
}
}
}
case 1:
{
lean_del_object(v___x_1151_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1139_);
if (v_flb_1142_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1141_);
if (v___x_1227_ == 0)
{
lean_object* v_out_1228_; lean_object* v_tagStack_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1246_; 
v_out_1228_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1229_ = lean_ctor_get(v___y_1129_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___y_1129_, 2);
lean_dec(v_unused_1247_);
v___x_1231_ = v___y_1129_;
v_isShared_1232_ = v_isSharedCheck_1246_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_tagStack_1229_);
lean_inc(v_out_1228_);
lean_dec(v___y_1129_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1246_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_out_x27_1240_; lean_object* v___x_1242_; 
v___x_1233_ = l_Int_toNat(v_indent_1148_);
lean_dec(v_indent_1148_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1233_);
v___x_1235_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1233_, v___x_1234_);
v___x_1236_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1235_, v_out_1228_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1229_);
v___x_1238_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1229_, v_tagStack_1229_, v_activeTags_1149_, v___x_1237_);
v___x_1239_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1229_);
lean_dec(v_tagStack_1229_);
v_out_x27_1240_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1236_, v___x_1238_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 2, v___x_1233_);
lean_ctor_set(v___x_1231_, 1, v___x_1239_);
lean_ctor_set(v___x_1231_, 0, v_out_x27_1240_);
v___x_1242_ = v___x_1231_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_out_x27_1240_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___x_1233_);
v___x_1242_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1243_;
v___y_1129_ = v___x_1242_;
goto _start;
}
}
}
else
{
lean_object* v_out_1248_; lean_object* v_tagStack_1249_; lean_object* v_column_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_indent_1148_);
v_out_1248_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1249_ = lean_ctor_get(v___y_1129_, 1);
v_column_1250_ = lean_ctor_get(v___y_1129_, 2);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1252_ = v___y_1129_;
v_isShared_1253_ = v_isSharedCheck_1267_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_column_1250_);
lean_inc(v_tagStack_1249_);
lean_inc(v_out_1248_);
lean_dec(v___y_1129_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1267_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_out_x27_1261_; lean_object* v___x_1263_; 
v___x_1254_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1255_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1254_, v_out_1248_);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v_column_1250_, v___x_1256_);
lean_dec(v_column_1250_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1249_);
v___x_1259_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1249_, v_tagStack_1249_, v_activeTags_1149_, v___x_1258_);
v___x_1260_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1249_);
lean_dec(v_tagStack_1249_);
v_out_x27_1261_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1255_, v___x_1259_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 2, v___x_1257_);
lean_ctor_set(v___x_1252_, 1, v___x_1260_);
lean_ctor_set(v___x_1252_, 0, v_out_x27_1261_);
v___x_1263_ = v___x_1252_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_out_x27_1261_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v___x_1257_);
v___x_1263_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1264_;
v___y_1129_ = v___x_1263_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = l_Int_toNat(v_indent_1148_);
lean_dec(v_indent_1148_);
v___x_1269_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1141_);
lean_dec(v_fla_1141_);
if (v___x_1269_ == 0)
{
lean_object* v_out_1270_; lean_object* v_tagStack_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1289_; 
v_out_1270_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1271_ = lean_ctor_get(v___y_1129_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___y_1129_, 2);
lean_dec(v_unused_1290_);
v___x_1273_ = v___y_1129_;
v_isShared_1274_ = v_isSharedCheck_1289_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_tagStack_1271_);
lean_inc(v_out_1270_);
lean_dec(v___y_1129_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1289_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_out_x27_1281_; lean_object* v___x_1283_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1268_, v___x_1275_);
v___x_1277_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1276_, v_out_1270_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1271_);
v___x_1279_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1271_, v_tagStack_1271_, v_activeTags_1149_, v___x_1278_);
v___x_1280_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1271_);
lean_dec(v_tagStack_1271_);
v_out_x27_1281_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1277_, v___x_1279_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 2, v___x_1268_);
lean_ctor_set(v___x_1273_, 1, v___x_1280_);
lean_ctor_set(v___x_1273_, 0, v_out_x27_1281_);
v___x_1283_ = v___x_1273_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_out_x27_1281_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v___x_1268_);
v___x_1283_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; 
v___x_1284_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1142_, v_tail_1143_, v_tail_1137_, v_w_1127_, v___x_1283_);
v_fst_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_fst_1285_);
v_snd_1286_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___x_1284_);
v_x_1128_ = v_fst_1285_;
v___y_1129_ = v_snd_1286_;
goto _start;
}
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_fst_1295_; 
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1292_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
v___x_1293_ = lean_nat_sub(v_w_1127_, v___x_1292_);
lean_inc(v_tail_1137_);
lean_inc(v_tail_1143_);
v___x_1294_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1142_, v_tail_1143_, v_tail_1137_, v___x_1293_, v___y_1129_);
lean_dec(v___x_1293_);
v_fst_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_fst_1295_);
if (lean_obj_tag(v_fst_1295_) == 1)
{
lean_object* v_head_1296_; lean_object* v_snd_1297_; lean_object* v_fla_1298_; uint8_t v___x_1299_; 
v_head_1296_ = lean_ctor_get(v_fst_1295_, 0);
v_snd_1297_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1297_);
lean_dec_ref(v___x_1294_);
v_fla_1298_ = lean_ctor_get(v_head_1296_, 0);
v___x_1299_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1298_);
if (v___x_1299_ == 0)
{
lean_object* v_out_1300_; lean_object* v_tagStack_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref_known(v_fst_1295_, 2);
v_out_1300_ = lean_ctor_get(v_snd_1297_, 0);
v_tagStack_1301_ = lean_ctor_get(v_snd_1297_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_snd_1297_, 2);
lean_dec(v_unused_1320_);
v___x_1303_ = v_snd_1297_;
v_isShared_1304_ = v_isSharedCheck_1319_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_tagStack_1301_);
lean_inc(v_out_1300_);
lean_dec(v_snd_1297_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1319_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_out_x27_1311_; lean_object* v___x_1313_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1268_);
v___x_1306_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1268_, v___x_1305_);
v___x_1307_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1306_, v_out_1300_);
v___x_1308_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1301_);
v___x_1309_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1301_, v_tagStack_1301_, v_activeTags_1149_, v___x_1308_);
v___x_1310_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1301_);
lean_dec(v_tagStack_1301_);
v_out_x27_1311_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1307_, v___x_1309_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 2, v___x_1268_);
lean_ctor_set(v___x_1303_, 1, v___x_1310_);
lean_ctor_set(v___x_1303_, 0, v_out_x27_1311_);
v___x_1313_ = v___x_1303_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_out_x27_1311_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v___x_1268_);
v___x_1313_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v_fst_1315_; lean_object* v_snd_1316_; 
v___x_1314_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1142_, v_tail_1143_, v_tail_1137_, v_w_1127_, v___x_1313_);
v_fst_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_fst_1315_);
v_snd_1316_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_snd_1316_);
lean_dec_ref(v___x_1314_);
v_x_1128_ = v_fst_1315_;
v___y_1129_ = v_snd_1316_;
goto _start;
}
}
}
else
{
lean_object* v_out_1321_; lean_object* v_tagStack_1322_; lean_object* v_column_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v___x_1268_);
lean_dec(v_tail_1143_);
lean_dec(v_tail_1137_);
v_out_1321_ = lean_ctor_get(v_snd_1297_, 0);
v_tagStack_1322_ = lean_ctor_get(v_snd_1297_, 1);
v_column_1323_ = lean_ctor_get(v_snd_1297_, 2);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1325_ = v_snd_1297_;
v_isShared_1326_ = v_isSharedCheck_1338_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_column_1323_);
lean_inc(v_tagStack_1322_);
lean_inc(v_out_1321_);
lean_dec(v_snd_1297_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1338_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_out_x27_1333_; lean_object* v___x_1335_; 
v___x_1327_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1291_, v_out_1321_);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_column_1323_, v___x_1328_);
lean_dec(v_column_1323_);
v___x_1330_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1322_);
v___x_1331_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1322_, v_tagStack_1322_, v_activeTags_1149_, v___x_1330_);
v___x_1332_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1322_);
lean_dec(v_tagStack_1322_);
v_out_x27_1333_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1327_, v___x_1331_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 2, v___x_1329_);
lean_ctor_set(v___x_1325_, 1, v___x_1332_);
lean_ctor_set(v___x_1325_, 0, v_out_x27_1333_);
v___x_1335_ = v___x_1325_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_out_x27_1333_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v___x_1329_);
v___x_1335_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
v_x_1128_ = v_fst_1295_;
v___y_1129_ = v___x_1335_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec(v_fst_1295_);
lean_dec(v___x_1268_);
lean_dec(v_activeTags_1149_);
lean_dec(v_tail_1143_);
lean_dec(v_tail_1137_);
v_snd_1339_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1339_);
lean_dec_ref(v___x_1294_);
v___x_1340_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2));
v___x_1341_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_1340_, v_snd_1339_);
return v___x_1341_;
}
}
}
}
case 2:
{
uint8_t v_force_1342_; uint8_t v___x_1343_; 
lean_del_object(v___x_1151_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1139_);
v_force_1342_ = lean_ctor_get_uint8(v_f_1147_, 0);
lean_dec_ref_known(v_f_1147_, 0);
v___x_1343_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1141_);
if (v___x_1343_ == 0)
{
v___y_1194_ = v___x_1343_;
goto v___jp_1193_;
}
else
{
if (v_force_1342_ == 0)
{
v___y_1194_ = v___x_1343_;
goto v___jp_1193_;
}
else
{
goto v___jp_1153_;
}
}
}
case 3:
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1139_);
v_a_1344_ = lean_ctor_get(v_f_1147_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_f_1147_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1346_ = v_f_1147_;
v_isShared_1347_ = v_isSharedCheck_1407_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v_f_1147_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1407_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint32_t v___x_1348_; lean_object* v_p_1349_; lean_object* v___x_1350_; uint8_t v_decide_1351_; 
v___x_1348_ = 10;
lean_inc_ref(v_a_1344_);
v_p_1349_ = lean_string_posof(v_a_1344_, v___x_1348_);
v___x_1350_ = lean_string_utf8_byte_size(v_a_1344_);
v_decide_1351_ = lean_nat_dec_eq(v_p_1349_, v___x_1350_);
if (v_decide_1351_ == 0)
{
lean_object* v_out_1352_; lean_object* v_tagStack_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1386_; 
v_out_1352_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1353_ = lean_ctor_get(v___y_1129_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___y_1129_, 2);
lean_dec(v_unused_1387_);
v___x_1355_ = v___y_1129_;
v_isShared_1356_ = v_isSharedCheck_1386_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_tagStack_1353_);
lean_inc(v_out_1352_);
lean_dec(v___y_1129_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1386_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_string_utf8_extract(v_a_1344_, v___x_1357_, v_p_1349_);
v___x_1359_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1358_, v_out_1352_);
v___x_1360_ = l_Int_toNat(v_indent_1148_);
v___x_1361_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1360_);
v___x_1362_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1360_, v___x_1361_);
v___x_1363_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1362_, v___x_1359_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 2, v___x_1360_);
lean_ctor_set(v___x_1355_, 0, v___x_1363_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_tagStack_1353_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v___x_1360_);
v___x_1365_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1366_ = lean_string_utf8_next(v_a_1344_, v_p_1349_);
lean_dec(v_p_1349_);
v___x_1367_ = lean_string_utf8_extract(v_a_1344_, v___x_1366_, v___x_1350_);
lean_dec(v___x_1366_);
lean_dec_ref(v_a_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1367_);
v___x_1369_ = v___x_1346_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1369_);
v___x_1371_ = v___x_1151_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_indent_1148_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_activeTags_1149_);
v___x_1371_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v_is_1373_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1371_);
v_is_1373_ = v___x_1145_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_tail_1143_);
v_is_1373_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_box(1);
v___x_1375_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1141_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v_fst_1377_; lean_object* v_snd_1378_; 
lean_dec(v_fla_1141_);
v___x_1376_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1142_, v_is_1373_, v_tail_1137_, v_w_1127_, v___x_1365_);
v_fst_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_fst_1377_);
v_snd_1378_ = lean_ctor_get(v___x_1376_, 1);
lean_inc(v_snd_1378_);
lean_dec_ref(v___x_1376_);
v_x_1128_ = v_fst_1377_;
v___y_1129_ = v_snd_1378_;
goto _start;
}
else
{
lean_object* v___x_1380_; 
v___x_1380_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_is_1373_);
v_x_1128_ = v___x_1380_;
v___y_1129_ = v___x_1365_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_out_1388_; lean_object* v_tagStack_1389_; lean_object* v_column_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_p_1349_);
lean_del_object(v___x_1346_);
lean_del_object(v___x_1151_);
lean_dec(v_indent_1148_);
lean_del_object(v___x_1145_);
v_out_1388_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1389_ = lean_ctor_get(v___y_1129_, 1);
v_column_1390_ = lean_ctor_get(v___y_1129_, 2);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1392_ = v___y_1129_;
v_isShared_1393_ = v_isSharedCheck_1406_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_column_1390_);
lean_inc(v_tagStack_1389_);
lean_inc(v_out_1388_);
lean_dec(v___y_1129_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1406_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_out_x27_1400_; lean_object* v___x_1402_; 
lean_inc_ref(v_a_1344_);
v___x_1394_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_1344_, v_out_1388_);
v___x_1395_ = lean_string_length(v_a_1344_);
lean_dec_ref(v_a_1344_);
v___x_1396_ = lean_nat_add(v_column_1390_, v___x_1395_);
lean_dec(v_column_1390_);
v___x_1397_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1389_);
v___x_1398_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1389_, v_tagStack_1389_, v_activeTags_1149_, v___x_1397_);
v___x_1399_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1389_);
lean_dec(v_tagStack_1389_);
v_out_x27_1400_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1394_, v___x_1398_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 2, v___x_1396_);
lean_ctor_set(v___x_1392_, 1, v___x_1399_);
lean_ctor_set(v___x_1392_, 0, v_out_x27_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_out_x27_1400_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v___x_1396_);
v___x_1402_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; 
v___x_1403_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1403_;
v___y_1129_ = v___x_1402_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1408_; lean_object* v_f_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_del_object(v___x_1139_);
v_indent_1408_ = lean_ctor_get(v_f_1147_, 0);
lean_inc(v_indent_1408_);
v_f_1409_ = lean_ctor_get(v_f_1147_, 1);
lean_inc(v_f_1409_);
lean_dec_ref_known(v_f_1147_, 2);
v___x_1410_ = lean_int_add(v_indent_1148_, v_indent_1408_);
lean_dec(v_indent_1408_);
lean_dec(v_indent_1148_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___x_1410_);
lean_ctor_set(v___x_1151_, 0, v_f_1409_);
v___x_1412_ = v___x_1151_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_f_1409_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_activeTags_1149_);
v___x_1412_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1412_);
v___x_1414_ = v___x_1145_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_tail_1143_);
v___x_1414_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v___x_1414_);
v_x_1128_ = v___x_1415_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1419_; lean_object* v_a_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v_a_1419_ = lean_ctor_get(v_f_1147_, 0);
lean_inc(v_a_1419_);
v_a_1420_ = lean_ctor_get(v_f_1147_, 1);
lean_inc(v_a_1420_);
lean_dec_ref_known(v_f_1147_, 2);
v___x_1421_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1148_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 2, v___x_1421_);
lean_ctor_set(v___x_1151_, 0, v_a_1419_);
v___x_1423_ = v___x_1151_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1419_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_indent_1148_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1424_, 0, v_a_1420_);
lean_ctor_set(v___x_1424_, 1, v_indent_1148_);
lean_ctor_set(v___x_1424_, 2, v_activeTags_1149_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1424_);
v___x_1426_ = v___x_1145_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_tail_1143_);
v___x_1426_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1426_);
lean_ctor_set(v___x_1139_, 0, v___x_1423_);
v___x_1428_ = v___x_1139_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v___x_1428_);
v_x_1128_ = v___x_1429_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1434_; uint8_t v_behavior_1435_; uint8_t v___x_1436_; 
lean_del_object(v___x_1139_);
v_a_1434_ = lean_ctor_get(v_f_1147_, 0);
lean_inc(v_a_1434_);
v_behavior_1435_ = lean_ctor_get_uint8(v_f_1147_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1147_, 1);
v___x_1436_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1141_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1438_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_a_1434_);
v___x_1438_ = v___x_1151_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1434_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_indent_1148_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_activeTags_1149_);
v___x_1438_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1439_);
lean_ctor_set(v___x_1145_, 0, v___x_1438_);
v___x_1441_ = v___x_1145_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_fst_1444_; lean_object* v_snd_1445_; 
v___x_1442_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v___x_1443_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_1435_, v___x_1441_, v___x_1442_, v_w_1127_, v___y_1129_);
v_fst_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_fst_1444_);
v_snd_1445_ = lean_ctor_get(v___x_1443_, 1);
lean_inc(v_snd_1445_);
lean_dec_ref(v___x_1443_);
v_x_1128_ = v_fst_1444_;
v___y_1129_ = v_snd_1445_;
goto _start;
}
}
}
else
{
lean_object* v___x_1450_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_a_1434_);
v___x_1450_ = v___x_1151_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1434_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_indent_1148_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_activeTags_1149_);
v___x_1450_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1450_);
v___x_1452_ = v___x_1145_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_tail_1143_);
v___x_1452_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v___x_1452_);
v_x_1128_ = v___x_1453_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1457_; lean_object* v_a_1458_; lean_object* v_out_1459_; lean_object* v_tagStack_1460_; lean_object* v_column_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1484_; 
v_a_1457_ = lean_ctor_get(v_f_1147_, 0);
lean_inc(v_a_1457_);
v_a_1458_ = lean_ctor_get(v_f_1147_, 1);
lean_inc(v_a_1458_);
lean_dec_ref_known(v_f_1147_, 2);
v_out_1459_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1460_ = lean_ctor_get(v___y_1129_, 1);
v_column_1461_ = lean_ctor_get(v___y_1129_, 2);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1463_ = v___y_1129_;
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_column_1461_);
lean_inc(v_tagStack_1460_);
lean_inc(v_out_1459_);
lean_dec(v___y_1129_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1465_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_1461_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_column_1461_);
lean_ctor_set(v___x_1466_, 1, v_out_1459_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_a_1457_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_tagStack_1460_);
lean_ctor_set(v___x_1145_, 0, v___x_1467_);
v___x_1469_ = v___x_1145_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_tagStack_1460_);
v___x_1469_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v___x_1469_);
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1471_ = v___x_1463_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_column_1461_);
v___x_1471_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v_activeTags_1149_, v___x_1472_);
lean_dec(v_activeTags_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 2, v___x_1473_);
lean_ctor_set(v___x_1151_, 0, v_a_1458_);
v___x_1475_ = v___x_1151_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1458_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_indent_1148_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_tail_1143_);
lean_ctor_set(v___x_1139_, 0, v___x_1475_);
v___x_1477_ = v___x_1139_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_tail_1143_);
v___x_1477_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v___x_1477_);
v_x_1128_ = v___x_1478_;
v___y_1129_ = v___x_1471_;
goto _start;
}
}
}
}
}
}
}
v___jp_1153_:
{
lean_object* v_out_1154_; lean_object* v_tagStack_1155_; lean_object* v_column_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1192_; 
v_out_1154_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1155_ = lean_ctor_get(v___y_1129_, 1);
v_column_1156_ = lean_ctor_get(v___y_1129_, 2);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1158_ = v___y_1129_;
v_isShared_1159_ = v_isSharedCheck_1192_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_column_1156_);
lean_inc(v_tagStack_1155_);
lean_inc(v_out_1154_);
lean_dec(v___y_1129_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1192_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
lean_inc(v_column_1156_);
v___x_1160_ = lean_nat_to_int(v_column_1156_);
v___x_1161_ = lean_int_dec_lt(v___x_1160_, v_indent_1148_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_out_x27_1169_; lean_object* v___x_1171_; 
lean_dec(v___x_1160_);
lean_dec(v_column_1156_);
v___x_1162_ = l_Int_toNat(v_indent_1148_);
lean_dec(v_indent_1148_);
v___x_1163_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1162_);
v___x_1164_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1162_, v___x_1163_);
v___x_1165_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1164_, v_out_1154_);
v___x_1166_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1155_);
v___x_1167_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1155_, v_tagStack_1155_, v_activeTags_1149_, v___x_1166_);
v___x_1168_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1155_);
lean_dec(v_tagStack_1155_);
v_out_x27_1169_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1165_, v___x_1167_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 2, v___x_1162_);
lean_ctor_set(v___x_1158_, 1, v___x_1168_);
lean_ctor_set(v___x_1158_, 0, v_out_x27_1169_);
v___x_1171_ = v___x_1158_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_out_x27_1169_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v___x_1162_);
v___x_1171_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1172_;
v___y_1129_ = v___x_1171_;
goto _start;
}
}
else
{
lean_object* v___x_1175_; uint32_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_out_x27_1186_; lean_object* v___x_1188_; 
v___x_1175_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_1176_ = 32;
v___x_1177_ = lean_int_sub(v_indent_1148_, v___x_1160_);
lean_dec(v___x_1160_);
lean_dec(v_indent_1148_);
v___x_1178_ = l_Int_toNat(v___x_1177_);
lean_dec(v___x_1177_);
v___x_1179_ = lean_string_pushn(v___x_1175_, v___x_1176_, v___x_1178_);
lean_inc_ref(v___x_1179_);
v___x_1180_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1179_, v_out_1154_);
v___x_1181_ = lean_string_length(v___x_1179_);
lean_dec_ref(v___x_1179_);
v___x_1182_ = lean_nat_add(v_column_1156_, v___x_1181_);
lean_dec(v_column_1156_);
v___x_1183_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1155_);
v___x_1184_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1155_, v_tagStack_1155_, v_activeTags_1149_, v___x_1183_);
v___x_1185_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1155_);
lean_dec(v_tagStack_1155_);
v_out_x27_1186_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1180_, v___x_1184_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 2, v___x_1182_);
lean_ctor_set(v___x_1158_, 1, v___x_1185_);
lean_ctor_set(v___x_1158_, 0, v_out_x27_1186_);
v___x_1188_ = v___x_1158_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_out_x27_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v___x_1182_);
v___x_1188_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1189_;
v___y_1129_ = v___x_1188_;
goto _start;
}
}
}
}
v___jp_1193_:
{
if (v___y_1194_ == 0)
{
goto v___jp_1153_;
}
else
{
lean_object* v_out_1195_; lean_object* v_tagStack_1196_; lean_object* v_column_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_indent_1148_);
v_out_1195_ = lean_ctor_get(v___y_1129_, 0);
v_tagStack_1196_ = lean_ctor_get(v___y_1129_, 1);
v_column_1197_ = lean_ctor_get(v___y_1129_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___y_1129_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1199_ = v___y_1129_;
v_isShared_1200_ = v_isSharedCheck_1210_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_column_1197_);
lean_inc(v_tagStack_1196_);
lean_inc(v_out_1195_);
lean_dec(v___y_1129_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1210_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_out_x27_1204_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1149_);
lean_inc(v_tagStack_1196_);
v___x_1202_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1196_, v_tagStack_1196_, v_activeTags_1149_, v___x_1201_);
v___x_1203_ = l_List_drop___redArg(v_activeTags_1149_, v_tagStack_1196_);
lean_dec(v_tagStack_1196_);
v_out_x27_1204_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1195_, v___x_1202_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1203_);
lean_ctor_set(v___x_1199_, 0, v_out_x27_1204_);
v___x_1206_ = v___x_1199_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_out_x27_1204_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_column_1197_);
v___x_1206_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1141_, v_flb_1142_, v_tail_1137_, v_tail_1143_);
v_x_1128_ = v___x_1207_;
v___y_1129_ = v___x_1206_;
goto _start;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object* v_w_1490_, lean_object* v_x_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1490_, v_x_1491_, v___y_1492_);
lean_dec(v_w_1490_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object* v_f_1494_, lean_object* v_w_1495_, lean_object* v_indent_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1498_ = lean_box(1);
v___x_1499_ = 0;
v___x_1500_ = lean_nat_to_int(v_indent_1496_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1502_, 0, v_f_1494_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
lean_ctor_set(v___x_1502_, 2, v___x_1501_);
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1505_, 0, v___x_1498_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
lean_ctor_set_uint8(v___x_1505_, sizeof(void*)*2, v___x_1499_);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1503_);
v___x_1507_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1495_, v___x_1506_, v___y_1497_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object* v_f_1508_, lean_object* v_w_1509_, lean_object* v_indent_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1508_, v_w_1509_, v_indent_1510_, v___y_1511_);
lean_dec(v_w_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object* v_f_1513_, lean_object* v_indent_1514_, lean_object* v_w_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_snd_1518_; lean_object* v_out_1519_; 
v___x_1516_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1));
v___x_1517_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1513_, v_w_1515_, v_indent_1514_, v___x_1516_);
v_snd_1518_ = lean_ctor_get(v___x_1517_, 1);
lean_inc(v_snd_1518_);
lean_dec_ref(v___x_1517_);
v_out_1519_ = lean_ctor_get(v_snd_1518_, 0);
lean_inc_ref(v_out_1519_);
lean_dec(v_snd_1518_);
return v_out_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object* v_f_1520_, lean_object* v_indent_1521_, lean_object* v_w_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_1520_, v_indent_1521_, v_w_1522_);
lean_dec(v_w_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_nat_to_int(v_a_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object* v_acc_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = lean_array_get_size(v_a_1527_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_nat_dec_eq(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1531_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText___closed__0, &l_Lean_Widget_instInhabitedTaggedText___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText___closed__0);
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_sub(v___x_1528_, v___x_1532_);
v___x_1534_ = lean_array_get_borrowed(v___x_1531_, v_a_1527_, v___x_1533_);
switch(lean_obj_tag(v___x_1534_))
{
case 0:
{
lean_object* v_a_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v___x_1533_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v___x_1536_ = lean_string_append(v_acc_1526_, v_a_1535_);
v___x_1537_ = lean_array_pop(v_a_1527_);
v_acc_1526_ = v___x_1536_;
v_a_1527_ = v___x_1537_;
goto _start;
}
case 1:
{
lean_object* v_a_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v___x_1533_);
v_a_1539_ = lean_ctor_get(v___x_1534_, 0);
lean_inc_ref(v_a_1539_);
v___x_1540_ = lean_array_pop(v_a_1527_);
v___x_1541_ = l_Array_reverse___redArg(v_a_1539_);
v___x_1542_ = l_Array_append___redArg(v___x_1540_, v___x_1541_);
lean_dec_ref(v___x_1541_);
v_a_1527_ = v___x_1542_;
goto _start;
}
default: 
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1534_, 1);
lean_inc_ref(v_a_1544_);
v___x_1545_ = lean_array_set(v_a_1527_, v___x_1533_, v_a_1544_);
lean_dec(v___x_1533_);
v_a_1527_ = v___x_1545_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_1527_);
return v_acc_1526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object* v_00_u03b1_1547_, lean_object* v_acc_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v_acc_1548_, v_a_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object* v_tt_1551_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1552_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_mk_empty_array_with_capacity(v___x_1553_);
v___x_1555_ = lean_array_push(v___x_1554_, v_tt_1551_);
v___x_1556_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v___x_1552_, v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object* v_00_u03b1_1557_, lean_object* v_tt_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1558_);
return v___x_1559_;
}
}
lean_object* runtime_initialize_Lean_Server_Rpc_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_TaggedText(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1 = _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Widget_TaggedText(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_TaggedText(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_TaggedText(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Widget_TaggedText(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Widget_TaggedText(builtin);
}
#ifdef __cplusplus
}
#endif

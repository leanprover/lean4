// Lean compiler output
// Module: Lean.Widget.TaggedText
// Imports: public import Lean.Server.Rpc.Basic import Init.Data.Array.GetLit
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
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
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0;
static lean_once_cell_t l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default;
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState;
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
static const lean_ctor_object l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)}};
static const lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Widget_TaggedText_prettyTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_TaggedText_prettyTagged___closed__0 = (const lean_object*)&l_Lean_Widget_TaggedText_prettyTagged___closed__0_value;
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
lean_dec_ref(v_t_13_);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object* v_a_64_){
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
lean_dec_ref(v_x_75_);
v_a_78_ = lean_ctor_get(v_x_76_, 0);
lean_inc_ref(v_a_78_);
lean_dec_ref(v_x_76_);
v___x_79_ = lean_string_dec_eq(v_a_77_, v_a_78_);
lean_dec_ref(v_a_78_);
lean_dec_ref(v_a_77_);
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
lean_dec_ref(v_x_75_);
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
lean_dec_ref(v_x_75_);
v_a_82_ = lean_ctor_get(v_x_76_, 0);
lean_inc_ref(v_a_82_);
lean_dec_ref(v_x_76_);
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
lean_dec_ref(v_x_75_);
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
lean_dec_ref(v_x_75_);
v_a_91_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v_x_76_, 1);
lean_inc_ref(v_a_92_);
lean_dec_ref(v_x_76_);
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
lean_dec_ref(v_x_75_);
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
lean_dec_ref(v_x_141_);
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
lean_dec_ref(v___x_246_);
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
lean_dec_ref(v___x_258_);
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
lean_dec_ref(v___x_282_);
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
lean_dec_ref(v___x_316_);
v_localinst_326_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg), 2, 1);
lean_closure_set(v_localinst_326_, 0, v_inst_228_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get(v___x_236_, v_a_325_, v___x_327_);
lean_dec(v_a_325_);
v___x_329_ = l_Array_fromJson_x3f___redArg(v_localinst_326_, v___x_328_);
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
return v___x_371_;
}
}
}
case 1:
{
lean_object* v_a_374_; lean_object* v_localinst_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_374_ = lean_ctor_get(v_x_360_, 0);
lean_inc_ref(v_a_374_);
lean_dec_ref(v_x_360_);
v_localinst_375_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson___redArg), 2, 1);
lean_closure_set(v_localinst_375_, 0, v_inst_359_);
v___x_376_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_377_ = l_Array_toJson___redArg(v_localinst_375_, v_a_374_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_Json_mkObj(v___x_380_);
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
lean_dec_ref(v_acc_460_);
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
lean_dec_ref(v_x_574_);
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
lean_inc(v_toBind_597_);
v_toPure_598_ = lean_ctor_get(v_toApplicative_596_, 1);
lean_inc(v_toPure_598_);
v_a_599_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_599_);
v_a_600_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_a_600_);
lean_dec_ref(v_x_574_);
lean_inc(v_toBind_597_);
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
lean_dec_ref(v_x_627_);
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
lean_dec_ref(v_x_627_);
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
lean_inc_ref(v_a_651_);
lean_dec_ref(v_x_627_);
lean_inc_ref(v_a_651_);
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
lean_dec_ref(v_x_680_);
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
lean_dec_ref(v_x_733_);
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
lean_dec_ref(v_x_733_);
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
lean_dec_ref(v___y_787_);
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
lean_dec_ref(v___x_788_);
v_rpcDecode_798_ = lean_ctor_get(v_inst_784_, 1);
lean_inc_ref(v_rpcDecode_798_);
lean_dec_ref(v_inst_784_);
v___x_654__overap_799_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_785_, v_rpcDecode_798_, v_a_797_);
v___x_800_ = lean_apply_1(v___x_654__overap_799_, v___y_787_);
return v___x_800_;
}
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9));
v___x_848_ = l_ReaderT_instMonad___redArg(v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22(void){
_start:
{
lean_object* v___x_849_; lean_object* v___f_850_; 
v___x_849_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_850_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_850_, 0, v___x_849_);
return v___f_850_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23(void){
_start:
{
lean_object* v___x_851_; lean_object* v___f_852_; 
v___x_851_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_852_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_852_, 0, v___x_851_);
return v___f_852_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24(void){
_start:
{
lean_object* v___x_853_; lean_object* v___f_854_; 
v___x_853_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_854_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_854_, 0, v___x_853_);
return v___f_854_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25(void){
_start:
{
lean_object* v___x_855_; lean_object* v___f_856_; 
v___x_855_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_856_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_856_, 0, v___x_855_);
return v___f_856_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_858_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_858_, 0, lean_box(0));
lean_closure_set(v___x_858_, 1, lean_box(0));
lean_closure_set(v___x_858_, 2, v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27(void){
_start:
{
lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___f_859_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22);
v___x_860_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___f_859_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_863_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_863_, 0, lean_box(0));
lean_closure_set(v___x_863_, 1, lean_box(0));
lean_closure_set(v___x_863_, 2, v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29(void){
_start:
{
lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___f_864_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25);
v___f_865_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24);
v___f_866_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23);
v___x_867_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28);
v___x_868_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27);
v___x_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___f_866_);
lean_ctor_set(v___x_869_, 3, v___f_865_);
lean_ctor_set(v___x_869_, 4, v___f_864_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_871_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_871_, 0, lean_box(0));
lean_closure_set(v___x_871_, 1, lean_box(0));
lean_closure_set(v___x_871_, 2, v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30);
v___x_873_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg(lean_object* v_inst_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___x_883_; 
v___x_877_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_878_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20));
lean_inc_ref(v_inst_876_);
v___f_879_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0), 5, 3);
lean_closure_set(v___f_879_, 0, v_inst_876_);
lean_closure_set(v___f_879_, 1, v___x_877_);
lean_closure_set(v___f_879_, 2, v___x_878_);
v___x_880_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31);
v___f_881_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32));
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1), 5, 3);
lean_closure_set(v___f_882_, 0, v___f_881_);
lean_closure_set(v___f_882_, 1, v_inst_876_);
lean_closure_set(v___f_882_, 2, v___x_880_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___f_879_);
lean_ctor_set(v___x_883_, 1, v___f_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable(lean_object* v_00_u03b1_884_, lean_object* v_inst_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_box(0);
v___x_890_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0);
v___x_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
lean_ctor_set(v___x_891_, 2, v___x_888_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default(void){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState(void){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default;
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object* v_s_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_out_896_; lean_object* v_tagStack_897_; lean_object* v_column_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_910_; 
v_out_896_ = lean_ctor_get(v___y_895_, 0);
v_tagStack_897_ = lean_ctor_get(v___y_895_, 1);
v_column_898_ = lean_ctor_get(v___y_895_, 2);
v_isSharedCheck_910_ = !lean_is_exclusive(v___y_895_);
if (v_isSharedCheck_910_ == 0)
{
v___x_900_ = v___y_895_;
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_column_898_);
lean_inc(v_tagStack_897_);
lean_inc(v_out_896_);
lean_dec(v___y_895_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_902_ = lean_box(0);
lean_inc_ref(v_s_894_);
v___x_903_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_894_, v_out_896_);
v___x_904_ = lean_string_length(v_s_894_);
lean_dec_ref(v_s_894_);
v___x_905_ = lean_nat_add(v_column_898_, v___x_904_);
lean_dec(v_column_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 2, v___x_905_);
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_907_ = v___x_900_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_tagStack_897_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v___x_905_);
v___x_907_ = v_reuseFailAlloc_909_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_902_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t v___x_911_, lean_object* v_s_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_string_push(v_s_912_, v___x_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object* v___x_914_, lean_object* v_s_915_){
_start:
{
uint32_t v___x_827__boxed_916_; lean_object* v_res_917_; 
v___x_827__boxed_916_ = lean_unbox_uint32(v___x_914_);
lean_dec(v___x_914_);
v_res_917_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_827__boxed_916_, v_s_915_);
return v_res_917_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_919_; lean_object* v___x_920_; 
v___x_919_ = 32;
v___x_920_ = lean_box_uint32(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___f_922_; 
v___x_921_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
v___f_922_ = lean_alloc_closure((void*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed), 2, 1);
lean_closure_set(v___f_922_, 0, v___x_921_);
return v___f_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object* v_indent_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_out_925_; lean_object* v_tagStack_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_939_; 
v_out_925_ = lean_ctor_get(v___y_924_, 0);
v_tagStack_926_ = lean_ctor_get(v___y_924_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v___y_924_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___y_924_, 2);
lean_dec(v_unused_940_);
v___x_928_ = v___y_924_;
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_tagStack_926_);
lean_inc(v_out_925_);
lean_dec(v___y_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_930_ = lean_box(0);
v___x_931_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
v___f_932_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
lean_inc(v_indent_923_);
v___x_933_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_932_, v_indent_923_, v___x_931_);
v___x_934_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_933_, v_out_925_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 2, v_indent_923_);
lean_ctor_set(v___x_928_, 0, v___x_934_);
v___x_936_ = v___x_928_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_tagStack_926_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_indent_923_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_930_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object* v_____do__lift_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_column_943_; lean_object* v___x_944_; 
v_column_943_ = lean_ctor_get(v_____do__lift_941_, 2);
lean_inc(v_column_943_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_column_943_);
lean_ctor_set(v___x_944_, 1, v___y_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object* v_____do__lift_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_945_, v___y_946_);
lean_dec_ref(v_____do__lift_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object* v_n_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_out_952_; lean_object* v_tagStack_953_; lean_object* v_column_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_967_; 
v_out_952_ = lean_ctor_get(v___y_951_, 0);
v_tagStack_953_ = lean_ctor_get(v___y_951_, 1);
v_column_954_ = lean_ctor_get(v___y_951_, 2);
v_isSharedCheck_967_ = !lean_is_exclusive(v___y_951_);
if (v_isSharedCheck_967_ == 0)
{
v___x_956_ = v___y_951_;
v_isShared_957_ = v_isSharedCheck_967_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_column_954_);
lean_inc(v_tagStack_953_);
lean_inc(v_out_952_);
lean_dec(v___y_951_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_967_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_958_ = lean_box(0);
v___x_959_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0));
lean_inc(v_column_954_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_column_954_);
lean_ctor_set(v___x_960_, 1, v_out_952_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v_n_950_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v_tagStack_953_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_962_);
lean_ctor_set(v___x_956_, 0, v___x_959_);
v___x_964_ = v___x_956_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_column_954_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_958_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object* v_acc_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_snd_970_; lean_object* v_fst_971_; lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_snd_970_ = lean_ctor_get(v_x_969_, 1);
lean_inc(v_snd_970_);
v_fst_971_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_fst_971_);
lean_dec_ref(v_x_969_);
v_fst_972_ = lean_ctor_get(v_snd_970_, 0);
v_snd_973_ = lean_ctor_get(v_snd_970_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_snd_970_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v_snd_970_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_972_);
lean_dec(v_snd_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v_fst_972_);
lean_ctor_set(v___x_975_, 0, v_fst_971_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_fst_971_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_fst_972_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_973_, v___x_978_, v_acc_968_);
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object* v___f_984_, lean_object* v_n_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_out_987_; lean_object* v_tagStack_988_; lean_object* v_column_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_out_987_ = lean_ctor_get(v___y_986_, 0);
v_tagStack_988_ = lean_ctor_get(v___y_986_, 1);
v_column_989_ = lean_ctor_get(v___y_986_, 2);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___y_986_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_991_ = v___y_986_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_column_989_);
lean_inc(v_tagStack_988_);
lean_inc(v_out_987_);
lean_dec(v___y_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_out_x27_997_; lean_object* v___x_999_; 
v___x_993_ = lean_box(0);
v___x_994_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_n_985_);
lean_inc(v_tagStack_988_);
v___x_995_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_988_, v_tagStack_988_, v_n_985_, v___x_994_);
v___x_996_ = l_List_drop___redArg(v_n_985_, v_tagStack_988_);
lean_dec(v_tagStack_988_);
v_out_x27_997_ = l_List_foldl___redArg(v___f_984_, v_out_987_, v___x_995_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_996_);
lean_ctor_set(v___x_991_, 0, v_out_x27_997_);
v___x_999_ = v___x_991_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_out_x27_997_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_column_989_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_993_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_zero_1025_; uint8_t v_isZero_1026_; 
v_zero_1025_ = lean_unsigned_to_nat(0u);
v_isZero_1026_ = lean_nat_dec_eq(v_x_1023_, v_zero_1025_);
if (v_isZero_1026_ == 1)
{
lean_dec(v_x_1023_);
return v_x_1024_;
}
else
{
uint32_t v___x_1027_; lean_object* v_one_1028_; lean_object* v_n_1029_; lean_object* v___x_1030_; 
v___x_1027_ = 32;
v_one_1028_ = lean_unsigned_to_nat(1u);
v_n_1029_ = lean_nat_sub(v_x_1023_, v_one_1028_);
lean_dec(v_x_1023_);
v___x_1030_ = lean_string_push(v_x_1024_, v___x_1027_);
v_x_1023_ = v_n_1029_;
v_x_1024_ = v___x_1030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object* v_fla_1032_, uint8_t v_flb_1033_, lean_object* v_tail_1034_, lean_object* v_is_x27_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1036_, 0, v_fla_1032_);
lean_ctor_set(v___x_1036_, 1, v_is_x27_1035_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*2, v_flb_1033_);
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v_tail_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object* v_fla_1038_, lean_object* v_flb_1039_, lean_object* v_tail_1040_, lean_object* v_is_x27_1041_){
_start:
{
uint8_t v_flb_5443__boxed_1042_; lean_object* v_res_1043_; 
v_flb_5443__boxed_1042_ = lean_unbox(v_flb_1039_);
v_res_1043_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1038_, v_flb_5443__boxed_1042_, v_tail_1040_, v_is_x27_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t v_flb_1044_, lean_object* v_items_1045_, lean_object* v_gs_1046_, lean_object* v_w_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v___y_1050_; lean_object* v_column_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v_g_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_r_1063_; lean_object* v___y_1065_; uint8_t v_foundLine_1070_; lean_object* v_space_1071_; uint8_t v___y_1073_; uint8_t v___x_1087_; 
v_column_1055_ = lean_ctor_get(v___y_1048_, 2);
v___x_1056_ = 0;
v___x_1057_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1044_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1058_, 0, v___x_1057_);
lean_inc(v_items_1045_);
v_g_1059_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1059_, 0, v___x_1058_);
lean_ctor_set(v_g_1059_, 1, v_items_1045_);
lean_ctor_set_uint8(v_g_1059_, sizeof(void*)*2, v_flb_1044_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_g_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_nat_sub(v_w_1047_, v_column_1055_);
lean_inc(v___x_1062_);
lean_inc(v_column_1055_);
v_r_1063_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1061_, v_column_1055_, v___x_1062_);
v_foundLine_1070_ = lean_ctor_get_uint8(v_r_1063_, sizeof(void*)*1);
v_space_1071_ = lean_ctor_get(v_r_1063_, 0);
lean_inc(v_space_1071_);
v___x_1087_ = lean_nat_dec_lt(v___x_1062_, v_space_1071_);
if (v___x_1087_ == 0)
{
v___y_1073_ = v_foundLine_1070_;
goto v___jp_1072_;
}
else
{
v___y_1073_ = v___x_1087_;
goto v___jp_1072_;
}
v___jp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1051_, 0, v___y_1050_);
v___x_1052_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_items_1045_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*2, v_flb_1044_);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_gs_1046_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___y_1048_);
return v___x_1054_;
}
v___jp_1064_:
{
uint8_t v_foundFlattenedHardLine_1066_; 
v_foundFlattenedHardLine_1066_ = lean_ctor_get_uint8(v_r_1063_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1063_);
if (v_foundFlattenedHardLine_1066_ == 0)
{
lean_object* v_space_1067_; uint8_t v___x_1068_; 
v_space_1067_ = lean_ctor_get(v___y_1065_, 0);
lean_inc(v_space_1067_);
lean_dec_ref(v___y_1065_);
v___x_1068_ = lean_nat_dec_le(v_space_1067_, v___x_1062_);
lean_dec(v___x_1062_);
lean_dec(v_space_1067_);
v___y_1050_ = v___x_1068_;
goto v___jp_1049_;
}
else
{
uint8_t v___x_1069_; 
lean_dec_ref(v___y_1065_);
lean_dec(v___x_1062_);
v___x_1069_ = 0;
v___y_1050_ = v___x_1069_;
goto v___jp_1049_;
}
}
v___jp_1072_:
{
if (v___y_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v_r_u2082_1075_; uint8_t v_foundLine_1076_; uint8_t v_foundFlattenedHardLine_1077_; lean_object* v_space_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v___x_1074_ = lean_nat_sub(v___x_1062_, v_space_1071_);
lean_inc(v_column_1055_);
lean_inc(v_gs_1046_);
v_r_u2082_1075_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1046_, v_column_1055_, v___x_1074_);
v_foundLine_1076_ = lean_ctor_get_uint8(v_r_u2082_1075_, sizeof(void*)*1);
v_foundFlattenedHardLine_1077_ = lean_ctor_get_uint8(v_r_u2082_1075_, sizeof(void*)*1 + 1);
v_space_1078_ = lean_ctor_get(v_r_u2082_1075_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_r_u2082_1075_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v_r_u2082_1075_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_space_1078_);
lean_dec(v_r_u2082_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_nat_add(v_space_1071_, v_space_1078_);
lean_dec(v_space_1078_);
lean_dec(v_space_1071_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*1, v_foundLine_1076_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1077_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v___y_1065_ = v___x_1084_;
goto v___jp_1064_;
}
}
}
else
{
lean_dec(v_space_1071_);
lean_inc_ref(v_r_1063_);
v___y_1065_ = v_r_1063_;
goto v___jp_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object* v_flb_1088_, lean_object* v_items_1089_, lean_object* v_gs_1090_, lean_object* v_w_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_flb_boxed_1093_; lean_object* v_res_1094_; 
v_flb_boxed_1093_ = lean_unbox(v_flb_1088_);
v_res_1094_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_1093_, v_items_1089_, v_gs_1090_, v_w_1091_, v___y_1092_);
lean_dec(v_w_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
return v_x_1095_;
}
else
{
lean_object* v_head_1097_; lean_object* v_snd_1098_; lean_object* v_tail_1099_; lean_object* v_fst_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1111_; 
v_head_1097_ = lean_ctor_get(v_x_1096_, 0);
lean_inc(v_head_1097_);
v_snd_1098_ = lean_ctor_get(v_head_1097_, 1);
lean_inc(v_snd_1098_);
v_tail_1099_ = lean_ctor_get(v_x_1096_, 1);
lean_inc(v_tail_1099_);
lean_dec_ref(v_x_1096_);
v_fst_1100_ = lean_ctor_get(v_head_1097_, 0);
lean_inc(v_fst_1100_);
lean_dec(v_head_1097_);
v_fst_1101_ = lean_ctor_get(v_snd_1098_, 0);
v_snd_1102_ = lean_ctor_get(v_snd_1098_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_snd_1098_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1104_ = v_snd_1098_;
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_snd_1102_);
lean_inc(v_fst_1101_);
lean_dec(v_snd_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v_fst_1101_);
lean_ctor_set(v___x_1104_, 0, v_fst_1100_);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fst_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_fst_1101_);
v___x_1107_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_1102_, v___x_1107_, v_x_1095_);
v_x_1095_ = v___x_1108_;
v_x_1096_ = v_tail_1099_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_1114_ = l_instInhabitedOfMonad___redArg(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object* v_msg_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_5381__overap_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_obj_once(&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0, &l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once, _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
v___x_5381__overap_1118_ = lean_panic_fn(v___x_1117_, v_msg_1115_);
v___x_1119_ = lean_apply_1(v___x_5381__overap_1118_, v___y_1116_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1122_ = lean_string_length(v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object* v_w_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___y_1126_);
return v___x_1128_;
}
else
{
lean_object* v_head_1129_; lean_object* v_items_1130_; 
v_head_1129_ = lean_ctor_get(v_x_1125_, 0);
v_items_1130_ = lean_ctor_get(v_head_1129_, 1);
lean_inc(v_items_1130_);
if (lean_obj_tag(v_items_1130_) == 0)
{
lean_object* v_tail_1131_; 
v_tail_1131_ = lean_ctor_get(v_x_1125_, 1);
lean_inc(v_tail_1131_);
lean_dec_ref(v_x_1125_);
v_x_1125_ = v_tail_1131_;
goto _start;
}
else
{
lean_object* v_head_1133_; lean_object* v_tail_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1447_; 
lean_inc(v_head_1129_);
v_head_1133_ = lean_ctor_get(v_items_1130_, 0);
lean_inc(v_head_1133_);
v_tail_1134_ = lean_ctor_get(v_x_1125_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1125_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_x_1125_, 0);
lean_dec(v_unused_1448_);
v___x_1136_ = v_x_1125_;
v_isShared_1137_ = v_isSharedCheck_1447_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_tail_1134_);
lean_dec(v_x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1447_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fla_1138_; uint8_t v_flb_1139_; lean_object* v_tail_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1445_; 
v_fla_1138_ = lean_ctor_get(v_head_1129_, 0);
lean_inc(v_fla_1138_);
v_flb_1139_ = lean_ctor_get_uint8(v_head_1129_, sizeof(void*)*2);
lean_dec(v_head_1129_);
v_tail_1140_ = lean_ctor_get(v_items_1130_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_items_1130_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v_items_1130_, 0);
lean_dec(v_unused_1446_);
v___x_1142_ = v_items_1130_;
v_isShared_1143_ = v_isSharedCheck_1445_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_tail_1140_);
lean_dec(v_items_1130_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1445_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_f_1144_; lean_object* v_indent_1145_; lean_object* v_activeTags_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1444_; 
v_f_1144_ = lean_ctor_get(v_head_1133_, 0);
v_indent_1145_ = lean_ctor_get(v_head_1133_, 1);
v_activeTags_1146_ = lean_ctor_get(v_head_1133_, 2);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_head_1133_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1148_ = v_head_1133_;
v_isShared_1149_ = v_isSharedCheck_1444_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_activeTags_1146_);
lean_inc(v_indent_1145_);
lean_inc(v_f_1144_);
lean_dec(v_head_1133_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1444_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_out_1151_; lean_object* v_tagStack_1152_; lean_object* v_column_1153_; uint8_t v___y_1193_; 
switch(lean_obj_tag(v_f_1144_))
{
case 0:
{
lean_object* v_out_1210_; lean_object* v_tagStack_1211_; lean_object* v_column_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1148_);
lean_dec(v_indent_1145_);
lean_del_object(v___x_1142_);
lean_del_object(v___x_1136_);
v_out_1210_ = lean_ctor_get(v___y_1126_, 0);
v_tagStack_1211_ = lean_ctor_get(v___y_1126_, 1);
v_column_1212_ = lean_ctor_get(v___y_1126_, 2);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1214_ = v___y_1126_;
v_isShared_1215_ = v_isSharedCheck_1225_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_column_1212_);
lean_inc(v_tagStack_1211_);
lean_inc(v_out_1210_);
lean_dec(v___y_1126_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1225_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_out_x27_1219_; lean_object* v___x_1221_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1211_);
v___x_1217_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1211_, v_tagStack_1211_, v_activeTags_1146_, v___x_1216_);
v___x_1218_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1211_);
lean_dec(v_tagStack_1211_);
v_out_x27_1219_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v_out_1210_, v___x_1217_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1218_);
lean_ctor_set(v___x_1214_, 0, v_out_x27_1219_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_out_x27_1219_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_column_1212_);
v___x_1221_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; 
v___x_1222_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v_tail_1140_);
v_x_1125_ = v___x_1222_;
v___y_1126_ = v___x_1221_;
goto _start;
}
}
}
case 1:
{
lean_del_object(v___x_1148_);
lean_del_object(v___x_1142_);
lean_del_object(v___x_1136_);
if (v_flb_1139_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1138_);
if (v___x_1226_ == 0)
{
lean_object* v_out_1227_; lean_object* v_tagStack_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_out_1227_ = lean_ctor_get(v___y_1126_, 0);
lean_inc_ref(v_out_1227_);
v_tagStack_1228_ = lean_ctor_get(v___y_1126_, 1);
lean_inc(v_tagStack_1228_);
lean_dec_ref(v___y_1126_);
v___x_1229_ = l_Int_toNat(v_indent_1145_);
lean_dec(v_indent_1145_);
v___x_1230_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1229_);
v___x_1231_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1231_, v_out_1227_);
v_out_1151_ = v___x_1232_;
v_tagStack_1152_ = v_tagStack_1228_;
v_column_1153_ = v___x_1229_;
goto v___jp_1150_;
}
else
{
lean_object* v_out_1233_; lean_object* v_tagStack_1234_; lean_object* v_column_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_indent_1145_);
v_out_1233_ = lean_ctor_get(v___y_1126_, 0);
lean_inc_ref(v_out_1233_);
v_tagStack_1234_ = lean_ctor_get(v___y_1126_, 1);
lean_inc(v_tagStack_1234_);
v_column_1235_ = lean_ctor_get(v___y_1126_, 2);
lean_inc(v_column_1235_);
lean_dec_ref(v___y_1126_);
v___x_1236_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1237_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1236_, v_out_1233_);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_column_1235_, v___x_1238_);
lean_dec(v_column_1235_);
v_out_1151_ = v___x_1237_;
v_tagStack_1152_ = v_tagStack_1234_;
v_column_1153_ = v___x_1239_;
goto v___jp_1150_;
}
}
else
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = l_Int_toNat(v_indent_1145_);
lean_dec(v_indent_1145_);
v___x_1241_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1138_);
lean_dec(v_fla_1138_);
if (v___x_1241_ == 0)
{
lean_object* v_out_1242_; lean_object* v_tagStack_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1261_; 
v_out_1242_ = lean_ctor_get(v___y_1126_, 0);
v_tagStack_1243_ = lean_ctor_get(v___y_1126_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___y_1126_, 2);
lean_dec(v_unused_1262_);
v___x_1245_ = v___y_1126_;
v_isShared_1246_ = v_isSharedCheck_1261_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_tagStack_1243_);
lean_inc(v_out_1242_);
lean_dec(v___y_1126_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1261_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_out_x27_1253_; lean_object* v___x_1255_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1240_);
v___x_1248_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1240_, v___x_1247_);
v___x_1249_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1248_, v_out_1242_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1243_);
v___x_1251_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1243_, v_tagStack_1243_, v_activeTags_1146_, v___x_1250_);
v___x_1252_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1243_);
lean_dec(v_tagStack_1243_);
v_out_x27_1253_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1249_, v___x_1251_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 2, v___x_1240_);
lean_ctor_set(v___x_1245_, 1, v___x_1252_);
lean_ctor_set(v___x_1245_, 0, v_out_x27_1253_);
v___x_1255_ = v___x_1245_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_out_x27_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v___x_1240_);
v___x_1255_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; 
v___x_1256_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1139_, v_tail_1140_, v_tail_1134_, v_w_1124_, v___x_1255_);
v_fst_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_fst_1257_);
v_snd_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_snd_1258_);
lean_dec_ref(v___x_1256_);
v_x_1125_ = v_fst_1257_;
v___y_1126_ = v_snd_1258_;
goto _start;
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_fst_1267_; 
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1264_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
v___x_1265_ = lean_nat_sub(v_w_1124_, v___x_1264_);
lean_inc(v_tail_1134_);
lean_inc(v_tail_1140_);
v___x_1266_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1139_, v_tail_1140_, v_tail_1134_, v___x_1265_, v___y_1126_);
lean_dec(v___x_1265_);
v_fst_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_fst_1267_);
if (lean_obj_tag(v_fst_1267_) == 1)
{
lean_object* v_head_1268_; lean_object* v_snd_1269_; lean_object* v_fla_1270_; uint8_t v___x_1271_; 
v_head_1268_ = lean_ctor_get(v_fst_1267_, 0);
v_snd_1269_ = lean_ctor_get(v___x_1266_, 1);
lean_inc(v_snd_1269_);
lean_dec_ref(v___x_1266_);
v_fla_1270_ = lean_ctor_get(v_head_1268_, 0);
v___x_1271_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1270_);
if (v___x_1271_ == 0)
{
lean_object* v_out_1272_; lean_object* v_tagStack_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_fst_1267_);
v_out_1272_ = lean_ctor_get(v_snd_1269_, 0);
v_tagStack_1273_ = lean_ctor_get(v_snd_1269_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_snd_1269_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v_snd_1269_, 2);
lean_dec(v_unused_1292_);
v___x_1275_ = v_snd_1269_;
v_isShared_1276_ = v_isSharedCheck_1291_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_tagStack_1273_);
lean_inc(v_out_1272_);
lean_dec(v_snd_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1291_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_out_x27_1283_; lean_object* v___x_1285_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1240_);
v___x_1278_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1240_, v___x_1277_);
v___x_1279_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1278_, v_out_1272_);
v___x_1280_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1273_);
v___x_1281_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1273_, v_tagStack_1273_, v_activeTags_1146_, v___x_1280_);
v___x_1282_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1273_);
lean_dec(v_tagStack_1273_);
v_out_x27_1283_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1279_, v___x_1281_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 2, v___x_1240_);
lean_ctor_set(v___x_1275_, 1, v___x_1282_);
lean_ctor_set(v___x_1275_, 0, v_out_x27_1283_);
v___x_1285_ = v___x_1275_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_out_x27_1283_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v___x_1240_);
v___x_1285_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v_fst_1287_; lean_object* v_snd_1288_; 
v___x_1286_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1139_, v_tail_1140_, v_tail_1134_, v_w_1124_, v___x_1285_);
v_fst_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_fst_1287_);
v_snd_1288_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_snd_1288_);
lean_dec_ref(v___x_1286_);
v_x_1125_ = v_fst_1287_;
v___y_1126_ = v_snd_1288_;
goto _start;
}
}
}
else
{
lean_object* v_out_1293_; lean_object* v_tagStack_1294_; lean_object* v_column_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___x_1240_);
lean_dec(v_tail_1140_);
lean_dec(v_tail_1134_);
v_out_1293_ = lean_ctor_get(v_snd_1269_, 0);
v_tagStack_1294_ = lean_ctor_get(v_snd_1269_, 1);
v_column_1295_ = lean_ctor_get(v_snd_1269_, 2);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_snd_1269_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1297_ = v_snd_1269_;
v_isShared_1298_ = v_isSharedCheck_1310_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_column_1295_);
lean_inc(v_tagStack_1294_);
lean_inc(v_out_1293_);
lean_dec(v_snd_1269_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1310_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_out_x27_1305_; lean_object* v___x_1307_; 
v___x_1299_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1263_, v_out_1293_);
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_add(v_column_1295_, v___x_1300_);
lean_dec(v_column_1295_);
v___x_1302_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1294_);
v___x_1303_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1294_, v_tagStack_1294_, v_activeTags_1146_, v___x_1302_);
v___x_1304_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1294_);
lean_dec(v_tagStack_1294_);
v_out_x27_1305_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1299_, v___x_1303_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 2, v___x_1301_);
lean_ctor_set(v___x_1297_, 1, v___x_1304_);
lean_ctor_set(v___x_1297_, 0, v_out_x27_1305_);
v___x_1307_ = v___x_1297_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_out_x27_1305_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v___x_1301_);
v___x_1307_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
v_x_1125_ = v_fst_1267_;
v___y_1126_ = v___x_1307_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec(v_fst_1267_);
lean_dec(v___x_1240_);
lean_dec(v_activeTags_1146_);
lean_dec(v_tail_1140_);
lean_dec(v_tail_1134_);
v_snd_1311_ = lean_ctor_get(v___x_1266_, 1);
lean_inc(v_snd_1311_);
lean_dec_ref(v___x_1266_);
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2));
v___x_1313_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_1312_, v_snd_1311_);
return v___x_1313_;
}
}
}
}
case 2:
{
uint8_t v_force_1314_; uint8_t v___x_1315_; 
lean_del_object(v___x_1148_);
lean_del_object(v___x_1142_);
lean_del_object(v___x_1136_);
v_force_1314_ = lean_ctor_get_uint8(v_f_1144_, 0);
lean_dec_ref(v_f_1144_);
v___x_1315_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1138_);
if (v___x_1315_ == 0)
{
v___y_1193_ = v___x_1315_;
goto v___jp_1192_;
}
else
{
if (v_force_1314_ == 0)
{
v___y_1193_ = v___x_1315_;
goto v___jp_1192_;
}
else
{
goto v___jp_1161_;
}
}
}
case 3:
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1366_; 
lean_del_object(v___x_1136_);
v_a_1316_ = lean_ctor_get(v_f_1144_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_f_1144_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1318_ = v_f_1144_;
v_isShared_1319_ = v_isSharedCheck_1366_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v_f_1144_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1366_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
uint32_t v___x_1320_; lean_object* v_p_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1320_ = 10;
lean_inc_ref(v_a_1316_);
v_p_1321_ = lean_string_posof(v_a_1316_, v___x_1320_);
v___x_1322_ = lean_string_utf8_byte_size(v_a_1316_);
v___x_1323_ = lean_nat_dec_eq(v_p_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v_out_1324_; lean_object* v_tagStack_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1358_; 
v_out_1324_ = lean_ctor_get(v___y_1126_, 0);
v_tagStack_1325_ = lean_ctor_get(v___y_1126_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___y_1126_, 2);
lean_dec(v_unused_1359_);
v___x_1327_ = v___y_1126_;
v_isShared_1328_ = v_isSharedCheck_1358_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_tagStack_1325_);
lean_inc(v_out_1324_);
lean_dec(v___y_1126_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1358_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_string_utf8_extract(v_a_1316_, v___x_1329_, v_p_1321_);
v___x_1331_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1330_, v_out_1324_);
v___x_1332_ = l_Int_toNat(v_indent_1145_);
v___x_1333_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1332_);
v___x_1334_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1332_, v___x_1333_);
v___x_1335_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1334_, v___x_1331_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 2, v___x_1332_);
lean_ctor_set(v___x_1327_, 0, v___x_1335_);
v___x_1337_ = v___x_1327_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_tagStack_1325_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v___x_1332_);
v___x_1337_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = lean_string_utf8_next(v_a_1316_, v_p_1321_);
lean_dec(v_p_1321_);
v___x_1339_ = lean_string_utf8_extract(v_a_1316_, v___x_1338_, v___x_1322_);
lean_dec(v___x_1338_);
lean_dec_ref(v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1339_);
v___x_1341_ = v___x_1318_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1341_);
v___x_1343_ = v___x_1148_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_indent_1145_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_activeTags_1146_);
v___x_1343_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v_is_1345_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1343_);
v_is_1345_ = v___x_1142_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_tail_1140_);
v_is_1345_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_box(1);
v___x_1347_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1138_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; 
lean_dec(v_fla_1138_);
v___x_1348_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1139_, v_is_1345_, v_tail_1134_, v_w_1124_, v___x_1337_);
v_fst_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_fst_1349_);
v_snd_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_snd_1350_);
lean_dec_ref(v___x_1348_);
v_x_1125_ = v_fst_1349_;
v___y_1126_ = v_snd_1350_;
goto _start;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v_is_1345_);
v_x_1125_ = v___x_1352_;
v___y_1126_ = v___x_1337_;
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
lean_object* v_out_1360_; lean_object* v_tagStack_1361_; lean_object* v_column_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_p_1321_);
lean_del_object(v___x_1318_);
lean_del_object(v___x_1148_);
lean_dec(v_indent_1145_);
lean_del_object(v___x_1142_);
v_out_1360_ = lean_ctor_get(v___y_1126_, 0);
lean_inc_ref(v_out_1360_);
v_tagStack_1361_ = lean_ctor_get(v___y_1126_, 1);
lean_inc(v_tagStack_1361_);
v_column_1362_ = lean_ctor_get(v___y_1126_, 2);
lean_inc(v_column_1362_);
lean_dec_ref(v___y_1126_);
lean_inc_ref(v_a_1316_);
v___x_1363_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_1316_, v_out_1360_);
v___x_1364_ = lean_string_length(v_a_1316_);
lean_dec_ref(v_a_1316_);
v___x_1365_ = lean_nat_add(v_column_1362_, v___x_1364_);
lean_dec(v_column_1362_);
v_out_1151_ = v___x_1363_;
v_tagStack_1152_ = v_tagStack_1361_;
v_column_1153_ = v___x_1365_;
goto v___jp_1150_;
}
}
}
case 4:
{
lean_object* v_indent_1367_; lean_object* v_f_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_del_object(v___x_1136_);
v_indent_1367_ = lean_ctor_get(v_f_1144_, 0);
lean_inc(v_indent_1367_);
v_f_1368_ = lean_ctor_get(v_f_1144_, 1);
lean_inc(v_f_1368_);
lean_dec_ref(v_f_1144_);
v___x_1369_ = lean_int_add(v_indent_1145_, v_indent_1367_);
lean_dec(v_indent_1367_);
lean_dec(v_indent_1145_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1369_);
lean_ctor_set(v___x_1148_, 0, v_f_1368_);
v___x_1371_ = v___x_1148_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_f_1368_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_activeTags_1146_);
v___x_1371_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1371_);
v___x_1373_ = v___x_1142_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_tail_1140_);
v___x_1373_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v___x_1373_);
v_x_1125_ = v___x_1374_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v_a_1378_ = lean_ctor_get(v_f_1144_, 0);
lean_inc(v_a_1378_);
v_a_1379_ = lean_ctor_get(v_f_1144_, 1);
lean_inc(v_a_1379_);
lean_dec_ref(v_f_1144_);
v___x_1380_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1145_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 2, v___x_1380_);
lean_ctor_set(v___x_1148_, 0, v_a_1378_);
v___x_1382_ = v___x_1148_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1378_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_indent_1145_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1379_);
lean_ctor_set(v___x_1383_, 1, v_indent_1145_);
lean_ctor_set(v___x_1383_, 2, v_activeTags_1146_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1383_);
v___x_1385_ = v___x_1142_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_tail_1140_);
v___x_1385_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1385_);
lean_ctor_set(v___x_1136_, 0, v___x_1382_);
v___x_1387_ = v___x_1136_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v___x_1387_);
v_x_1125_ = v___x_1388_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1393_; uint8_t v_behavior_1394_; uint8_t v___x_1395_; 
lean_del_object(v___x_1136_);
v_a_1393_ = lean_ctor_get(v_f_1144_, 0);
lean_inc(v_a_1393_);
v_behavior_1394_ = lean_ctor_get_uint8(v_f_1144_, sizeof(void*)*1);
lean_dec_ref(v_f_1144_);
v___x_1395_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1138_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1397_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1393_);
v___x_1397_ = v___x_1148_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1393_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_indent_1145_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_activeTags_1146_);
v___x_1397_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_box(0);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1398_);
lean_ctor_set(v___x_1142_, 0, v___x_1397_);
v___x_1400_ = v___x_1142_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; 
v___x_1401_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v_tail_1140_);
v___x_1402_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_1394_, v___x_1400_, v___x_1401_, v_w_1124_, v___y_1126_);
v_fst_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_fst_1403_);
v_snd_1404_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_snd_1404_);
lean_dec_ref(v___x_1402_);
v_x_1125_ = v_fst_1403_;
v___y_1126_ = v_snd_1404_;
goto _start;
}
}
}
else
{
lean_object* v___x_1409_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1393_);
v___x_1409_ = v___x_1148_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_indent_1145_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_activeTags_1146_);
v___x_1409_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1409_);
v___x_1411_ = v___x_1142_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_tail_1140_);
v___x_1411_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v___x_1411_);
v_x_1125_ = v___x_1412_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1416_; lean_object* v_a_1417_; lean_object* v_out_1418_; lean_object* v_tagStack_1419_; lean_object* v_column_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1443_; 
v_a_1416_ = lean_ctor_get(v_f_1144_, 0);
lean_inc(v_a_1416_);
v_a_1417_ = lean_ctor_get(v_f_1144_, 1);
lean_inc(v_a_1417_);
lean_dec_ref(v_f_1144_);
v_out_1418_ = lean_ctor_get(v___y_1126_, 0);
v_tagStack_1419_ = lean_ctor_get(v___y_1126_, 1);
v_column_1420_ = lean_ctor_get(v___y_1126_, 2);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1422_ = v___y_1126_;
v_isShared_1423_ = v_isSharedCheck_1443_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_column_1420_);
lean_inc(v_tagStack_1419_);
lean_inc(v_out_1418_);
lean_dec(v___y_1126_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1443_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0));
lean_inc(v_column_1420_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_column_1420_);
lean_ctor_set(v___x_1425_, 1, v_out_1418_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_a_1416_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_tagStack_1419_);
lean_ctor_set(v___x_1142_, 0, v___x_1426_);
v___x_1428_ = v___x_1142_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_tagStack_1419_);
v___x_1428_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1430_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v___x_1428_);
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1430_ = v___x_1422_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_column_1420_);
v___x_1430_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_add(v_activeTags_1146_, v___x_1431_);
lean_dec(v_activeTags_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 2, v___x_1432_);
lean_ctor_set(v___x_1148_, 0, v_a_1417_);
v___x_1434_ = v___x_1148_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1417_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_indent_1145_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v_tail_1140_);
lean_ctor_set(v___x_1136_, 0, v___x_1434_);
v___x_1436_ = v___x_1136_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_tail_1140_);
v___x_1436_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v___x_1436_);
v_x_1125_ = v___x_1437_;
v___y_1126_ = v___x_1430_;
goto _start;
}
}
}
}
}
}
}
v___jp_1150_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_out_x27_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1152_);
v___x_1155_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1152_, v_tagStack_1152_, v_activeTags_1146_, v___x_1154_);
v___x_1156_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1152_);
lean_dec(v_tagStack_1152_);
v_out_x27_1157_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v_out_1151_, v___x_1155_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_out_x27_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
lean_ctor_set(v___x_1158_, 2, v_column_1153_);
v___x_1159_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v_tail_1140_);
v_x_1125_ = v___x_1159_;
v___y_1126_ = v___x_1158_;
goto _start;
}
v___jp_1161_:
{
lean_object* v_out_1162_; lean_object* v_tagStack_1163_; lean_object* v_column_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1191_; 
v_out_1162_ = lean_ctor_get(v___y_1126_, 0);
v_tagStack_1163_ = lean_ctor_get(v___y_1126_, 1);
v_column_1164_ = lean_ctor_get(v___y_1126_, 2);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1166_ = v___y_1126_;
v_isShared_1167_ = v_isSharedCheck_1191_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_column_1164_);
lean_inc(v_tagStack_1163_);
lean_inc(v_out_1162_);
lean_dec(v___y_1126_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1191_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
lean_inc(v_column_1164_);
v___x_1168_ = lean_nat_to_int(v_column_1164_);
v___x_1169_ = lean_int_dec_lt(v___x_1168_, v_indent_1145_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_out_x27_1177_; lean_object* v___x_1179_; 
lean_dec(v___x_1168_);
lean_dec(v_column_1164_);
v___x_1170_ = l_Int_toNat(v_indent_1145_);
lean_dec(v_indent_1145_);
v___x_1171_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1170_);
v___x_1172_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1170_, v___x_1171_);
v___x_1173_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1172_, v_out_1162_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1163_);
v___x_1175_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1163_, v_tagStack_1163_, v_activeTags_1146_, v___x_1174_);
v___x_1176_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1163_);
lean_dec(v_tagStack_1163_);
v_out_x27_1177_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1173_, v___x_1175_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 2, v___x_1170_);
lean_ctor_set(v___x_1166_, 1, v___x_1176_);
lean_ctor_set(v___x_1166_, 0, v_out_x27_1177_);
v___x_1179_ = v___x_1166_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_out_x27_1177_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v___x_1170_);
v___x_1179_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v_tail_1140_);
v_x_1125_ = v___x_1180_;
v___y_1126_ = v___x_1179_;
goto _start;
}
}
else
{
lean_object* v___x_1183_; uint32_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_del_object(v___x_1166_);
v___x_1183_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_1184_ = 32;
v___x_1185_ = lean_int_sub(v_indent_1145_, v___x_1168_);
lean_dec(v___x_1168_);
lean_dec(v_indent_1145_);
v___x_1186_ = l_Int_toNat(v___x_1185_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_string_pushn(v___x_1183_, v___x_1184_, v___x_1186_);
lean_inc_ref(v___x_1187_);
v___x_1188_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1187_, v_out_1162_);
v___x_1189_ = lean_string_length(v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1190_ = lean_nat_add(v_column_1164_, v___x_1189_);
lean_dec(v_column_1164_);
v_out_1151_ = v___x_1188_;
v_tagStack_1152_ = v_tagStack_1163_;
v_column_1153_ = v___x_1190_;
goto v___jp_1150_;
}
}
}
v___jp_1192_:
{
if (v___y_1193_ == 0)
{
goto v___jp_1161_;
}
else
{
lean_object* v_out_1194_; lean_object* v_tagStack_1195_; lean_object* v_column_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_indent_1145_);
v_out_1194_ = lean_ctor_get(v___y_1126_, 0);
v_tagStack_1195_ = lean_ctor_get(v___y_1126_, 1);
v_column_1196_ = lean_ctor_get(v___y_1126_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1198_ = v___y_1126_;
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_column_1196_);
lean_inc(v_tagStack_1195_);
lean_inc(v_out_1194_);
lean_dec(v___y_1126_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v_out_x27_1203_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1146_);
lean_inc(v_tagStack_1195_);
v___x_1201_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1195_, v_tagStack_1195_, v_activeTags_1146_, v___x_1200_);
v___x_1202_ = l_List_drop___redArg(v_activeTags_1146_, v_tagStack_1195_);
lean_dec(v_tagStack_1195_);
v_out_x27_1203_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v_out_1194_, v___x_1201_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v___x_1202_);
lean_ctor_set(v___x_1198_, 0, v_out_x27_1203_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_out_x27_1203_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_column_1196_);
v___x_1205_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1138_, v_flb_1139_, v_tail_1134_, v_tail_1140_);
v_x_1125_ = v___x_1206_;
v___y_1126_ = v___x_1205_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object* v_w_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1449_, v_x_1450_, v___y_1451_);
lean_dec(v_w_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object* v_f_1453_, lean_object* v_w_1454_, lean_object* v_indent_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1457_ = lean_box(1);
v___x_1458_ = 0;
v___x_1459_ = lean_nat_to_int(v_indent_1455_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1461_, 0, v_f_1453_);
lean_ctor_set(v___x_1461_, 1, v___x_1459_);
lean_ctor_set(v___x_1461_, 2, v___x_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1464_, 0, v___x_1457_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*2, v___x_1458_);
v___x_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
lean_ctor_set(v___x_1465_, 1, v___x_1462_);
v___x_1466_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1454_, v___x_1465_, v___y_1456_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object* v_f_1467_, lean_object* v_w_1468_, lean_object* v_indent_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1467_, v_w_1468_, v_indent_1469_, v___y_1470_);
lean_dec(v_w_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object* v_f_1476_, lean_object* v_indent_1477_, lean_object* v_w_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_snd_1481_; lean_object* v_out_1482_; 
v___x_1479_ = ((lean_object*)(l_Lean_Widget_TaggedText_prettyTagged___closed__0));
v___x_1480_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1476_, v_w_1478_, v_indent_1477_, v___x_1479_);
v_snd_1481_ = lean_ctor_get(v___x_1480_, 1);
lean_inc(v_snd_1481_);
lean_dec_ref(v___x_1480_);
v_out_1482_ = lean_ctor_get(v_snd_1481_, 0);
lean_inc_ref(v_out_1482_);
lean_dec(v_snd_1481_);
return v_out_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object* v_f_1483_, lean_object* v_indent_1484_, lean_object* v_w_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_1483_, v_indent_1484_, v_w_1485_);
lean_dec(v_w_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_nat_to_int(v_a_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object* v_acc_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = lean_array_get_size(v_a_1490_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_nat_dec_eq(v___x_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText___closed__0, &l_Lean_Widget_instInhabitedTaggedText___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText___closed__0);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_sub(v___x_1491_, v___x_1495_);
v___x_1497_ = lean_array_get_borrowed(v___x_1494_, v_a_1490_, v___x_1496_);
switch(lean_obj_tag(v___x_1497_))
{
case 0:
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v___x_1496_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v___x_1499_ = lean_string_append(v_acc_1489_, v_a_1498_);
v___x_1500_ = lean_array_pop(v_a_1490_);
v_acc_1489_ = v___x_1499_;
v_a_1490_ = v___x_1500_;
goto _start;
}
case 1:
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v___x_1496_);
v_a_1502_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_a_1502_);
v___x_1503_ = lean_array_pop(v_a_1490_);
v___x_1504_ = l_Array_reverse___redArg(v_a_1502_);
v___x_1505_ = l_Array_append___redArg(v___x_1503_, v___x_1504_);
lean_dec_ref(v___x_1504_);
v_a_1490_ = v___x_1505_;
goto _start;
}
default: 
{
lean_object* v_a_1507_; lean_object* v___x_1508_; 
v_a_1507_ = lean_ctor_get(v___x_1497_, 1);
lean_inc_ref(v_a_1507_);
v___x_1508_ = lean_array_set(v_a_1490_, v___x_1496_, v_a_1507_);
lean_dec(v___x_1496_);
v_a_1490_ = v___x_1508_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_1490_);
return v_acc_1489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object* v_00_u03b1_1510_, lean_object* v_acc_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v_acc_1511_, v_a_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object* v_tt_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1515_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_mk_empty_array_with_capacity(v___x_1516_);
v___x_1518_ = lean_array_push(v___x_1517_, v_tt_1514_);
v___x_1519_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v___x_1515_, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object* v_00_u03b1_1520_, lean_object* v_tt_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1521_);
return v___x_1522_;
}
}
lean_object* runtime_initialize_Lean_Server_Rpc_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_TaggedText(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default = _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default();
lean_mark_persistent(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default);
l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState = _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState();
lean_mark_persistent(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState);
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

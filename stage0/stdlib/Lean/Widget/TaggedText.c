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
lean_inc_n(v_toBind_597_, 2);
v_toPure_598_ = lean_ctor_get(v_toApplicative_596_, 1);
lean_inc(v_toPure_598_);
v_a_599_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_599_);
v_a_600_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_a_600_);
lean_dec_ref(v_x_574_);
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
lean_inc_ref_n(v_a_651_, 2);
lean_dec_ref(v_x_627_);
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
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0(void){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_box(0);
v___x_896_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0);
v___x_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_894_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default(void){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState_default;
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object* v_s_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_out_902_; lean_object* v_tagStack_903_; lean_object* v_column_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_916_; 
v_out_902_ = lean_ctor_get(v___y_901_, 0);
v_tagStack_903_ = lean_ctor_get(v___y_901_, 1);
v_column_904_ = lean_ctor_get(v___y_901_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v___y_901_);
if (v_isSharedCheck_916_ == 0)
{
v___x_906_ = v___y_901_;
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_column_904_);
lean_inc(v_tagStack_903_);
lean_inc(v_out_902_);
lean_dec(v___y_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_908_ = lean_box(0);
lean_inc_ref(v_s_900_);
v___x_909_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_900_, v_out_902_);
v___x_910_ = lean_string_length(v_s_900_);
lean_dec_ref(v_s_900_);
v___x_911_ = lean_nat_add(v_column_904_, v___x_910_);
lean_dec(v_column_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_911_);
lean_ctor_set(v___x_906_, 0, v___x_909_);
v___x_913_ = v___x_906_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_tagStack_903_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v___x_911_);
v___x_913_ = v_reuseFailAlloc_915_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_908_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t v___x_917_, lean_object* v_s_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = lean_string_push(v_s_918_, v___x_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object* v___x_920_, lean_object* v_s_921_){
_start:
{
uint32_t v___x_827__boxed_922_; lean_object* v_res_923_; 
v___x_827__boxed_922_ = lean_unbox_uint32(v___x_920_);
lean_dec(v___x_920_);
v_res_923_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_827__boxed_922_, v_s_921_);
return v_res_923_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_925_; lean_object* v___x_926_; 
v___x_925_ = 32;
v___x_926_ = lean_box_uint32(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___f_928_; 
v___x_927_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
v___f_928_ = lean_alloc_closure((void*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed), 2, 1);
lean_closure_set(v___f_928_, 0, v___x_927_);
return v___f_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object* v_indent_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_out_931_; lean_object* v_tagStack_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_945_; 
v_out_931_ = lean_ctor_get(v___y_930_, 0);
v_tagStack_932_ = lean_ctor_get(v___y_930_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v___y_930_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___y_930_, 2);
lean_dec(v_unused_946_);
v___x_934_ = v___y_930_;
v_isShared_935_ = v_isSharedCheck_945_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_tagStack_932_);
lean_inc(v_out_931_);
lean_dec(v___y_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_945_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_936_ = lean_box(0);
v___x_937_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
v___f_938_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
lean_inc(v_indent_929_);
v___x_939_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_938_, v_indent_929_, v___x_937_);
v___x_940_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_939_, v_out_931_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 2, v_indent_929_);
lean_ctor_set(v___x_934_, 0, v___x_940_);
v___x_942_ = v___x_934_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_tagStack_932_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_indent_929_);
v___x_942_ = v_reuseFailAlloc_944_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_936_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object* v_____do__lift_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_column_949_; lean_object* v___x_950_; 
v_column_949_ = lean_ctor_get(v_____do__lift_947_, 2);
lean_inc(v_column_949_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_column_949_);
lean_ctor_set(v___x_950_, 1, v___y_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object* v_____do__lift_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_951_, v___y_952_);
lean_dec_ref(v_____do__lift_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object* v_n_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_out_958_; lean_object* v_tagStack_959_; lean_object* v_column_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_973_; 
v_out_958_ = lean_ctor_get(v___y_957_, 0);
v_tagStack_959_ = lean_ctor_get(v___y_957_, 1);
v_column_960_ = lean_ctor_get(v___y_957_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v___y_957_);
if (v_isSharedCheck_973_ == 0)
{
v___x_962_ = v___y_957_;
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_column_960_);
lean_inc(v_tagStack_959_);
lean_inc(v_out_958_);
lean_dec(v___y_957_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_964_ = lean_box(0);
v___x_965_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0));
lean_inc(v_column_960_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_column_960_);
lean_ctor_set(v___x_966_, 1, v_out_958_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_n_956_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_tagStack_959_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_968_);
lean_ctor_set(v___x_962_, 0, v___x_965_);
v___x_970_ = v___x_962_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_column_960_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_964_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object* v_acc_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_snd_976_; lean_object* v_fst_977_; lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_snd_976_ = lean_ctor_get(v_x_975_, 1);
lean_inc(v_snd_976_);
v_fst_977_ = lean_ctor_get(v_x_975_, 0);
lean_inc(v_fst_977_);
lean_dec_ref(v_x_975_);
v_fst_978_ = lean_ctor_get(v_snd_976_, 0);
v_snd_979_ = lean_ctor_get(v_snd_976_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_snd_976_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v_snd_976_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_snd_979_);
lean_inc(v_fst_978_);
lean_dec(v_snd_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_fst_978_);
lean_ctor_set(v___x_981_, 0, v_fst_977_);
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_fst_978_);
v___x_984_ = v_reuseFailAlloc_986_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_979_, v___x_984_, v_acc_974_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object* v___f_990_, lean_object* v_n_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_out_993_; lean_object* v_tagStack_994_; lean_object* v_column_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1008_; 
v_out_993_ = lean_ctor_get(v___y_992_, 0);
v_tagStack_994_ = lean_ctor_get(v___y_992_, 1);
v_column_995_ = lean_ctor_get(v___y_992_, 2);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___y_992_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_997_ = v___y_992_;
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_column_995_);
lean_inc(v_tagStack_994_);
lean_inc(v_out_993_);
lean_dec(v___y_992_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_out_x27_1003_; lean_object* v___x_1005_; 
v___x_999_ = lean_box(0);
v___x_1000_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_n_991_);
lean_inc(v_tagStack_994_);
v___x_1001_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_994_, v_tagStack_994_, v_n_991_, v___x_1000_);
v___x_1002_ = l_List_drop___redArg(v_n_991_, v_tagStack_994_);
lean_dec(v_tagStack_994_);
v_out_x27_1003_ = l_List_foldl___redArg(v___f_990_, v_out_993_, v___x_1001_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1002_);
lean_ctor_set(v___x_997_, 0, v_out_x27_1003_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_out_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_column_995_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_999_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
lean_object* v_zero_1031_; uint8_t v_isZero_1032_; 
v_zero_1031_ = lean_unsigned_to_nat(0u);
v_isZero_1032_ = lean_nat_dec_eq(v_x_1029_, v_zero_1031_);
if (v_isZero_1032_ == 1)
{
lean_dec(v_x_1029_);
return v_x_1030_;
}
else
{
uint32_t v___x_1033_; lean_object* v_one_1034_; lean_object* v_n_1035_; lean_object* v___x_1036_; 
v___x_1033_ = 32;
v_one_1034_ = lean_unsigned_to_nat(1u);
v_n_1035_ = lean_nat_sub(v_x_1029_, v_one_1034_);
lean_dec(v_x_1029_);
v___x_1036_ = lean_string_push(v_x_1030_, v___x_1033_);
v_x_1029_ = v_n_1035_;
v_x_1030_ = v___x_1036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object* v_fla_1038_, uint8_t v_flb_1039_, lean_object* v_tail_1040_, lean_object* v_is_x27_1041_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1042_, 0, v_fla_1038_);
lean_ctor_set(v___x_1042_, 1, v_is_x27_1041_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*2, v_flb_1039_);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_tail_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object* v_fla_1044_, lean_object* v_flb_1045_, lean_object* v_tail_1046_, lean_object* v_is_x27_1047_){
_start:
{
uint8_t v_flb_6181__boxed_1048_; lean_object* v_res_1049_; 
v_flb_6181__boxed_1048_ = lean_unbox(v_flb_1045_);
v_res_1049_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1044_, v_flb_6181__boxed_1048_, v_tail_1046_, v_is_x27_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t v_flb_1050_, lean_object* v_items_1051_, lean_object* v_gs_1052_, lean_object* v_w_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v___y_1056_; lean_object* v_column_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v_g_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_r_1069_; lean_object* v___y_1071_; uint8_t v_foundLine_1076_; lean_object* v_space_1077_; uint8_t v___y_1079_; uint8_t v___x_1093_; 
v_column_1061_ = lean_ctor_get(v___y_1054_, 2);
v___x_1062_ = 0;
v___x_1063_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1050_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1064_, 0, v___x_1063_);
lean_inc(v_items_1051_);
v_g_1065_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1065_, 0, v___x_1064_);
lean_ctor_set(v_g_1065_, 1, v_items_1051_);
lean_ctor_set_uint8(v_g_1065_, sizeof(void*)*2, v_flb_1050_);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_g_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_nat_sub(v_w_1053_, v_column_1061_);
lean_inc(v___x_1068_);
lean_inc(v_column_1061_);
v_r_1069_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1067_, v_column_1061_, v___x_1068_);
v_foundLine_1076_ = lean_ctor_get_uint8(v_r_1069_, sizeof(void*)*1);
v_space_1077_ = lean_ctor_get(v_r_1069_, 0);
lean_inc(v_space_1077_);
v___x_1093_ = lean_nat_dec_lt(v___x_1068_, v_space_1077_);
if (v___x_1093_ == 0)
{
v___y_1079_ = v_foundLine_1076_;
goto v___jp_1078_;
}
else
{
v___y_1079_ = v___x_1093_;
goto v___jp_1078_;
}
v___jp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1057_, 0, v___y_1056_);
v___x_1058_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_items_1051_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*2, v_flb_1050_);
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_gs_1052_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___y_1054_);
return v___x_1060_;
}
v___jp_1070_:
{
uint8_t v_foundFlattenedHardLine_1072_; 
v_foundFlattenedHardLine_1072_ = lean_ctor_get_uint8(v_r_1069_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1069_);
if (v_foundFlattenedHardLine_1072_ == 0)
{
lean_object* v_space_1073_; uint8_t v___x_1074_; 
v_space_1073_ = lean_ctor_get(v___y_1071_, 0);
lean_inc(v_space_1073_);
lean_dec_ref(v___y_1071_);
v___x_1074_ = lean_nat_dec_le(v_space_1073_, v___x_1068_);
lean_dec(v___x_1068_);
lean_dec(v_space_1073_);
v___y_1056_ = v___x_1074_;
goto v___jp_1055_;
}
else
{
uint8_t v___x_1075_; 
lean_dec_ref(v___y_1071_);
lean_dec(v___x_1068_);
v___x_1075_ = 0;
v___y_1056_ = v___x_1075_;
goto v___jp_1055_;
}
}
v___jp_1078_:
{
if (v___y_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v_r_u2082_1081_; uint8_t v_foundLine_1082_; uint8_t v_foundFlattenedHardLine_1083_; lean_object* v_space_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1092_; 
v___x_1080_ = lean_nat_sub(v___x_1068_, v_space_1077_);
lean_inc(v_column_1061_);
lean_inc(v_gs_1052_);
v_r_u2082_1081_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1052_, v_column_1061_, v___x_1080_);
v_foundLine_1082_ = lean_ctor_get_uint8(v_r_u2082_1081_, sizeof(void*)*1);
v_foundFlattenedHardLine_1083_ = lean_ctor_get_uint8(v_r_u2082_1081_, sizeof(void*)*1 + 1);
v_space_1084_ = lean_ctor_get(v_r_u2082_1081_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_r_u2082_1081_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1086_ = v_r_u2082_1081_;
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_space_1084_);
lean_dec(v_r_u2082_1081_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_nat_add(v_space_1077_, v_space_1084_);
lean_dec(v_space_1084_);
lean_dec(v_space_1077_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*1, v_foundLine_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1083_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v___y_1071_ = v___x_1090_;
goto v___jp_1070_;
}
}
}
else
{
lean_dec(v_space_1077_);
lean_inc_ref(v_r_1069_);
v___y_1071_ = v_r_1069_;
goto v___jp_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object* v_flb_1094_, lean_object* v_items_1095_, lean_object* v_gs_1096_, lean_object* v_w_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_flb_boxed_1099_; lean_object* v_res_1100_; 
v_flb_boxed_1099_ = lean_unbox(v_flb_1094_);
v_res_1100_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_1099_, v_items_1095_, v_gs_1096_, v_w_1097_, v___y_1098_);
lean_dec(v_w_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
return v_x_1101_;
}
else
{
lean_object* v_head_1103_; lean_object* v_snd_1104_; lean_object* v_tail_1105_; lean_object* v_fst_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1117_; 
v_head_1103_ = lean_ctor_get(v_x_1102_, 0);
lean_inc(v_head_1103_);
v_snd_1104_ = lean_ctor_get(v_head_1103_, 1);
lean_inc(v_snd_1104_);
v_tail_1105_ = lean_ctor_get(v_x_1102_, 1);
lean_inc(v_tail_1105_);
lean_dec_ref(v_x_1102_);
v_fst_1106_ = lean_ctor_get(v_head_1103_, 0);
lean_inc(v_fst_1106_);
lean_dec(v_head_1103_);
v_fst_1107_ = lean_ctor_get(v_snd_1104_, 0);
v_snd_1108_ = lean_ctor_get(v_snd_1104_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_snd_1104_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1110_ = v_snd_1104_;
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snd_1108_);
lean_inc(v_fst_1107_);
lean_dec(v_snd_1104_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_fst_1107_);
lean_ctor_set(v___x_1110_, 0, v_fst_1106_);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_fst_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_fst_1107_);
v___x_1113_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_1108_, v___x_1113_, v_x_1101_);
v_x_1101_ = v___x_1114_;
v_x_1102_ = v_tail_1105_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_1120_ = l_instInhabitedOfMonad___redArg(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object* v_msg_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_6132__overap_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_obj_once(&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0, &l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once, _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
v___x_6132__overap_1124_ = lean_panic_fn_borrowed(v___x_1123_, v_msg_1121_);
v___x_1125_ = lean_apply_1(v___x_6132__overap_1124_, v___y_1122_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1128_ = lean_string_length(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object* v_w_1130_, lean_object* v_x_1131_, lean_object* v___y_1132_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___y_1132_);
return v___x_1134_;
}
else
{
lean_object* v_head_1135_; lean_object* v_items_1136_; 
v_head_1135_ = lean_ctor_get(v_x_1131_, 0);
v_items_1136_ = lean_ctor_get(v_head_1135_, 1);
lean_inc(v_items_1136_);
if (lean_obj_tag(v_items_1136_) == 0)
{
lean_object* v_tail_1137_; 
v_tail_1137_ = lean_ctor_get(v_x_1131_, 1);
lean_inc(v_tail_1137_);
lean_dec_ref(v_x_1131_);
v_x_1131_ = v_tail_1137_;
goto _start;
}
else
{
lean_object* v_head_1139_; lean_object* v_tail_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1491_; 
lean_inc(v_head_1135_);
v_head_1139_ = lean_ctor_get(v_items_1136_, 0);
lean_inc(v_head_1139_);
v_tail_1140_ = lean_ctor_get(v_x_1131_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_x_1131_, 0);
lean_dec(v_unused_1492_);
v___x_1142_ = v_x_1131_;
v_isShared_1143_ = v_isSharedCheck_1491_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_tail_1140_);
lean_dec(v_x_1131_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1491_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_fla_1144_; uint8_t v_flb_1145_; lean_object* v_tail_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1489_; 
v_fla_1144_ = lean_ctor_get(v_head_1135_, 0);
lean_inc(v_fla_1144_);
v_flb_1145_ = lean_ctor_get_uint8(v_head_1135_, sizeof(void*)*2);
lean_dec(v_head_1135_);
v_tail_1146_ = lean_ctor_get(v_items_1136_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_items_1136_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_items_1136_, 0);
lean_dec(v_unused_1490_);
v___x_1148_ = v_items_1136_;
v_isShared_1149_ = v_isSharedCheck_1489_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_tail_1146_);
lean_dec(v_items_1136_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1489_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_f_1150_; lean_object* v_indent_1151_; lean_object* v_activeTags_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1488_; 
v_f_1150_ = lean_ctor_get(v_head_1139_, 0);
v_indent_1151_ = lean_ctor_get(v_head_1139_, 1);
v_activeTags_1152_ = lean_ctor_get(v_head_1139_, 2);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_head_1139_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1154_ = v_head_1139_;
v_isShared_1155_ = v_isSharedCheck_1488_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_activeTags_1152_);
lean_inc(v_indent_1151_);
lean_inc(v_f_1150_);
lean_dec(v_head_1139_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1488_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint8_t v___y_1197_; 
switch(lean_obj_tag(v_f_1150_))
{
case 0:
{
lean_object* v_out_1214_; lean_object* v_tagStack_1215_; lean_object* v_column_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1229_; 
lean_del_object(v___x_1154_);
lean_dec(v_indent_1151_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1142_);
v_out_1214_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1215_ = lean_ctor_get(v___y_1132_, 1);
v_column_1216_ = lean_ctor_get(v___y_1132_, 2);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1218_ = v___y_1132_;
v_isShared_1219_ = v_isSharedCheck_1229_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_column_1216_);
lean_inc(v_tagStack_1215_);
lean_inc(v_out_1214_);
lean_dec(v___y_1132_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1229_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_out_x27_1223_; lean_object* v___x_1225_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1215_);
v___x_1221_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1215_, v_tagStack_1215_, v_activeTags_1152_, v___x_1220_);
v___x_1222_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1215_);
lean_dec(v_tagStack_1215_);
v_out_x27_1223_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1214_, v___x_1221_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1222_);
lean_ctor_set(v___x_1218_, 0, v_out_x27_1223_);
v___x_1225_ = v___x_1218_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_out_x27_1223_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_column_1216_);
v___x_1225_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; 
v___x_1226_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1226_;
v___y_1132_ = v___x_1225_;
goto _start;
}
}
}
case 1:
{
lean_del_object(v___x_1154_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1142_);
if (v_flb_1145_ == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1144_);
if (v___x_1230_ == 0)
{
lean_object* v_out_1231_; lean_object* v_tagStack_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1249_; 
v_out_1231_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1232_ = lean_ctor_get(v___y_1132_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___y_1132_, 2);
lean_dec(v_unused_1250_);
v___x_1234_ = v___y_1132_;
v_isShared_1235_ = v_isSharedCheck_1249_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_tagStack_1232_);
lean_inc(v_out_1231_);
lean_dec(v___y_1132_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1249_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_out_x27_1243_; lean_object* v___x_1245_; 
v___x_1236_ = l_Int_toNat(v_indent_1151_);
lean_dec(v_indent_1151_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1236_);
v___x_1238_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1236_, v___x_1237_);
v___x_1239_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1238_, v_out_1231_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1232_);
v___x_1241_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1232_, v_tagStack_1232_, v_activeTags_1152_, v___x_1240_);
v___x_1242_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1232_);
lean_dec(v_tagStack_1232_);
v_out_x27_1243_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1239_, v___x_1241_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 2, v___x_1236_);
lean_ctor_set(v___x_1234_, 1, v___x_1242_);
lean_ctor_set(v___x_1234_, 0, v_out_x27_1243_);
v___x_1245_ = v___x_1234_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_out_x27_1243_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v___x_1236_);
v___x_1245_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1246_;
v___y_1132_ = v___x_1245_;
goto _start;
}
}
}
else
{
lean_object* v_out_1251_; lean_object* v_tagStack_1252_; lean_object* v_column_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v_indent_1151_);
v_out_1251_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1252_ = lean_ctor_get(v___y_1132_, 1);
v_column_1253_ = lean_ctor_get(v___y_1132_, 2);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1255_ = v___y_1132_;
v_isShared_1256_ = v_isSharedCheck_1270_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_column_1253_);
lean_inc(v_tagStack_1252_);
lean_inc(v_out_1251_);
lean_dec(v___y_1132_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1270_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_out_x27_1264_; lean_object* v___x_1266_; 
v___x_1257_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1258_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1257_, v_out_1251_);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_add(v_column_1253_, v___x_1259_);
lean_dec(v_column_1253_);
v___x_1261_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1252_);
v___x_1262_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1252_, v_tagStack_1252_, v_activeTags_1152_, v___x_1261_);
v___x_1263_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1252_);
lean_dec(v_tagStack_1252_);
v_out_x27_1264_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1258_, v___x_1262_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 2, v___x_1260_);
lean_ctor_set(v___x_1255_, 1, v___x_1263_);
lean_ctor_set(v___x_1255_, 0, v_out_x27_1264_);
v___x_1266_ = v___x_1255_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_out_x27_1264_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v___x_1260_);
v___x_1266_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1267_;
v___y_1132_ = v___x_1266_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = l_Int_toNat(v_indent_1151_);
lean_dec(v_indent_1151_);
v___x_1272_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1144_);
lean_dec(v_fla_1144_);
if (v___x_1272_ == 0)
{
lean_object* v_out_1273_; lean_object* v_tagStack_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1292_; 
v_out_1273_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1274_ = lean_ctor_get(v___y_1132_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___y_1132_, 2);
lean_dec(v_unused_1293_);
v___x_1276_ = v___y_1132_;
v_isShared_1277_ = v_isSharedCheck_1292_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_tagStack_1274_);
lean_inc(v_out_1273_);
lean_dec(v___y_1132_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1292_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_out_x27_1284_; lean_object* v___x_1286_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1271_);
v___x_1279_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1271_, v___x_1278_);
v___x_1280_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1279_, v_out_1273_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1274_);
v___x_1282_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1274_, v_tagStack_1274_, v_activeTags_1152_, v___x_1281_);
v___x_1283_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1274_);
lean_dec(v_tagStack_1274_);
v_out_x27_1284_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1280_, v___x_1282_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 2, v___x_1271_);
lean_ctor_set(v___x_1276_, 1, v___x_1283_);
lean_ctor_set(v___x_1276_, 0, v_out_x27_1284_);
v___x_1286_ = v___x_1276_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_out_x27_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1271_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; 
v___x_1287_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1145_, v_tail_1146_, v_tail_1140_, v_w_1130_, v___x_1286_);
v_fst_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1289_);
lean_dec_ref(v___x_1287_);
v_x_1131_ = v_fst_1288_;
v___y_1132_ = v_snd_1289_;
goto _start;
}
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_fst_1298_; 
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1295_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
v___x_1296_ = lean_nat_sub(v_w_1130_, v___x_1295_);
lean_inc(v_tail_1140_);
lean_inc(v_tail_1146_);
v___x_1297_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1145_, v_tail_1146_, v_tail_1140_, v___x_1296_, v___y_1132_);
lean_dec(v___x_1296_);
v_fst_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_fst_1298_);
if (lean_obj_tag(v_fst_1298_) == 1)
{
lean_object* v_head_1299_; lean_object* v_snd_1300_; lean_object* v_fla_1301_; uint8_t v___x_1302_; 
v_head_1299_ = lean_ctor_get(v_fst_1298_, 0);
v_snd_1300_ = lean_ctor_get(v___x_1297_, 1);
lean_inc(v_snd_1300_);
lean_dec_ref(v___x_1297_);
v_fla_1301_ = lean_ctor_get(v_head_1299_, 0);
v___x_1302_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1301_);
if (v___x_1302_ == 0)
{
lean_object* v_out_1303_; lean_object* v_tagStack_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_fst_1298_);
v_out_1303_ = lean_ctor_get(v_snd_1300_, 0);
v_tagStack_1304_ = lean_ctor_get(v_snd_1300_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_snd_1300_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_snd_1300_, 2);
lean_dec(v_unused_1323_);
v___x_1306_ = v_snd_1300_;
v_isShared_1307_ = v_isSharedCheck_1322_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_tagStack_1304_);
lean_inc(v_out_1303_);
lean_dec(v_snd_1300_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1322_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_out_x27_1314_; lean_object* v___x_1316_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1271_);
v___x_1309_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1271_, v___x_1308_);
v___x_1310_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1309_, v_out_1303_);
v___x_1311_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1304_);
v___x_1312_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1304_, v_tagStack_1304_, v_activeTags_1152_, v___x_1311_);
v___x_1313_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1304_);
lean_dec(v_tagStack_1304_);
v_out_x27_1314_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1310_, v___x_1312_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 2, v___x_1271_);
lean_ctor_set(v___x_1306_, 1, v___x_1313_);
lean_ctor_set(v___x_1306_, 0, v_out_x27_1314_);
v___x_1316_ = v___x_1306_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_out_x27_1314_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v___x_1271_);
v___x_1316_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v_fst_1318_; lean_object* v_snd_1319_; 
v___x_1317_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1145_, v_tail_1146_, v_tail_1140_, v_w_1130_, v___x_1316_);
v_fst_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_fst_1318_);
v_snd_1319_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1319_);
lean_dec_ref(v___x_1317_);
v_x_1131_ = v_fst_1318_;
v___y_1132_ = v_snd_1319_;
goto _start;
}
}
}
else
{
lean_object* v_out_1324_; lean_object* v_tagStack_1325_; lean_object* v_column_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v___x_1271_);
lean_dec(v_tail_1146_);
lean_dec(v_tail_1140_);
v_out_1324_ = lean_ctor_get(v_snd_1300_, 0);
v_tagStack_1325_ = lean_ctor_get(v_snd_1300_, 1);
v_column_1326_ = lean_ctor_get(v_snd_1300_, 2);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_snd_1300_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1328_ = v_snd_1300_;
v_isShared_1329_ = v_isSharedCheck_1341_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_column_1326_);
lean_inc(v_tagStack_1325_);
lean_inc(v_out_1324_);
lean_dec(v_snd_1300_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1341_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_out_x27_1336_; lean_object* v___x_1338_; 
v___x_1330_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1294_, v_out_1324_);
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v_column_1326_, v___x_1331_);
lean_dec(v_column_1326_);
v___x_1333_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1325_);
v___x_1334_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1325_, v_tagStack_1325_, v_activeTags_1152_, v___x_1333_);
v___x_1335_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1325_);
lean_dec(v_tagStack_1325_);
v_out_x27_1336_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1330_, v___x_1334_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 2, v___x_1332_);
lean_ctor_set(v___x_1328_, 1, v___x_1335_);
lean_ctor_set(v___x_1328_, 0, v_out_x27_1336_);
v___x_1338_ = v___x_1328_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_out_x27_1336_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v___x_1332_);
v___x_1338_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
v_x_1131_ = v_fst_1298_;
v___y_1132_ = v___x_1338_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_fst_1298_);
lean_dec(v___x_1271_);
lean_dec(v_activeTags_1152_);
lean_dec(v_tail_1146_);
lean_dec(v_tail_1140_);
v_snd_1342_ = lean_ctor_get(v___x_1297_, 1);
lean_inc(v_snd_1342_);
lean_dec_ref(v___x_1297_);
v___x_1343_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2));
v___x_1344_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_1343_, v_snd_1342_);
return v___x_1344_;
}
}
}
}
case 2:
{
uint8_t v_force_1345_; uint8_t v___x_1346_; 
lean_del_object(v___x_1154_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1142_);
v_force_1345_ = lean_ctor_get_uint8(v_f_1150_, 0);
lean_dec_ref(v_f_1150_);
v___x_1346_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1144_);
if (v___x_1346_ == 0)
{
v___y_1197_ = v___x_1346_;
goto v___jp_1196_;
}
else
{
if (v_force_1345_ == 0)
{
v___y_1197_ = v___x_1346_;
goto v___jp_1196_;
}
else
{
goto v___jp_1156_;
}
}
}
case 3:
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1410_; 
lean_del_object(v___x_1142_);
v_a_1347_ = lean_ctor_get(v_f_1150_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_f_1150_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1349_ = v_f_1150_;
v_isShared_1350_ = v_isSharedCheck_1410_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v_f_1150_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1410_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
uint32_t v___x_1351_; lean_object* v_p_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1351_ = 10;
lean_inc_ref(v_a_1347_);
v_p_1352_ = lean_string_posof(v_a_1347_, v___x_1351_);
v___x_1353_ = lean_string_utf8_byte_size(v_a_1347_);
v___x_1354_ = lean_nat_dec_eq(v_p_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v_out_1355_; lean_object* v_tagStack_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1389_; 
v_out_1355_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1356_ = lean_ctor_get(v___y_1132_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v___y_1132_, 2);
lean_dec(v_unused_1390_);
v___x_1358_ = v___y_1132_;
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_tagStack_1356_);
lean_inc(v_out_1355_);
lean_dec(v___y_1132_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_string_utf8_extract(v_a_1347_, v___x_1360_, v_p_1352_);
v___x_1362_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1361_, v_out_1355_);
v___x_1363_ = l_Int_toNat(v_indent_1151_);
v___x_1364_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1363_);
v___x_1365_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1363_, v___x_1364_);
v___x_1366_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1365_, v___x_1362_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 2, v___x_1363_);
lean_ctor_set(v___x_1358_, 0, v___x_1366_);
v___x_1368_ = v___x_1358_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_tagStack_1356_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v___x_1363_);
v___x_1368_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = lean_string_utf8_next(v_a_1347_, v_p_1352_);
lean_dec(v_p_1352_);
v___x_1370_ = lean_string_utf8_extract(v_a_1347_, v___x_1369_, v___x_1353_);
lean_dec(v___x_1369_);
lean_dec_ref(v_a_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1370_);
v___x_1372_ = v___x_1349_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1372_);
v___x_1374_ = v___x_1154_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_indent_1151_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_activeTags_1152_);
v___x_1374_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v_is_1376_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1374_);
v_is_1376_ = v___x_1148_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_tail_1146_);
v_is_1376_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_box(1);
v___x_1378_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1144_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; 
lean_dec(v_fla_1144_);
v___x_1379_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1145_, v_is_1376_, v_tail_1140_, v_w_1130_, v___x_1368_);
v_fst_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_fst_1380_);
v_snd_1381_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_snd_1381_);
lean_dec_ref(v___x_1379_);
v_x_1131_ = v_fst_1380_;
v___y_1132_ = v_snd_1381_;
goto _start;
}
else
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_is_1376_);
v_x_1131_ = v___x_1383_;
v___y_1132_ = v___x_1368_;
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
lean_object* v_out_1391_; lean_object* v_tagStack_1392_; lean_object* v_column_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_p_1352_);
lean_del_object(v___x_1349_);
lean_del_object(v___x_1154_);
lean_dec(v_indent_1151_);
lean_del_object(v___x_1148_);
v_out_1391_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1392_ = lean_ctor_get(v___y_1132_, 1);
v_column_1393_ = lean_ctor_get(v___y_1132_, 2);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1395_ = v___y_1132_;
v_isShared_1396_ = v_isSharedCheck_1409_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_column_1393_);
lean_inc(v_tagStack_1392_);
lean_inc(v_out_1391_);
lean_dec(v___y_1132_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1409_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_out_x27_1403_; lean_object* v___x_1405_; 
lean_inc_ref(v_a_1347_);
v___x_1397_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_1347_, v_out_1391_);
v___x_1398_ = lean_string_length(v_a_1347_);
lean_dec_ref(v_a_1347_);
v___x_1399_ = lean_nat_add(v_column_1393_, v___x_1398_);
lean_dec(v_column_1393_);
v___x_1400_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1392_);
v___x_1401_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1392_, v_tagStack_1392_, v_activeTags_1152_, v___x_1400_);
v___x_1402_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1392_);
lean_dec(v_tagStack_1392_);
v_out_x27_1403_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1397_, v___x_1401_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 2, v___x_1399_);
lean_ctor_set(v___x_1395_, 1, v___x_1402_);
lean_ctor_set(v___x_1395_, 0, v_out_x27_1403_);
v___x_1405_ = v___x_1395_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_out_x27_1403_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v___x_1399_);
v___x_1405_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1406_;
v___y_1132_ = v___x_1405_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1411_; lean_object* v_f_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_del_object(v___x_1142_);
v_indent_1411_ = lean_ctor_get(v_f_1150_, 0);
lean_inc(v_indent_1411_);
v_f_1412_ = lean_ctor_get(v_f_1150_, 1);
lean_inc(v_f_1412_);
lean_dec_ref(v_f_1150_);
v___x_1413_ = lean_int_add(v_indent_1151_, v_indent_1411_);
lean_dec(v_indent_1411_);
lean_dec(v_indent_1151_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1413_);
lean_ctor_set(v___x_1154_, 0, v_f_1412_);
v___x_1415_ = v___x_1154_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_f_1412_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_activeTags_1152_);
v___x_1415_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1415_);
v___x_1417_ = v___x_1148_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_tail_1146_);
v___x_1417_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v___x_1417_);
v_x_1131_ = v___x_1418_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v_a_1422_ = lean_ctor_get(v_f_1150_, 0);
lean_inc(v_a_1422_);
v_a_1423_ = lean_ctor_get(v_f_1150_, 1);
lean_inc(v_a_1423_);
lean_dec_ref(v_f_1150_);
v___x_1424_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1151_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 2, v___x_1424_);
lean_ctor_set(v___x_1154_, 0, v_a_1422_);
v___x_1426_ = v___x_1154_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1422_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_indent_1151_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1427_, 0, v_a_1423_);
lean_ctor_set(v___x_1427_, 1, v_indent_1151_);
lean_ctor_set(v___x_1427_, 2, v_activeTags_1152_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1427_);
v___x_1429_ = v___x_1148_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_tail_1146_);
v___x_1429_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1429_);
lean_ctor_set(v___x_1142_, 0, v___x_1426_);
v___x_1431_ = v___x_1142_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; 
v___x_1432_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v___x_1431_);
v_x_1131_ = v___x_1432_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1437_; uint8_t v_behavior_1438_; uint8_t v___x_1439_; 
lean_del_object(v___x_1142_);
v_a_1437_ = lean_ctor_get(v_f_1150_, 0);
lean_inc(v_a_1437_);
v_behavior_1438_ = lean_ctor_get_uint8(v_f_1150_, sizeof(void*)*1);
lean_dec_ref(v_f_1150_);
v___x_1439_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1144_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1441_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_a_1437_);
v___x_1441_ = v___x_1154_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1437_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_indent_1151_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_activeTags_1152_);
v___x_1441_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_box(0);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1442_);
lean_ctor_set(v___x_1148_, 0, v___x_1441_);
v___x_1444_ = v___x_1148_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_fst_1447_; lean_object* v_snd_1448_; 
v___x_1445_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v___x_1446_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_1438_, v___x_1444_, v___x_1445_, v_w_1130_, v___y_1132_);
v_fst_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_fst_1447_);
v_snd_1448_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_snd_1448_);
lean_dec_ref(v___x_1446_);
v_x_1131_ = v_fst_1447_;
v___y_1132_ = v_snd_1448_;
goto _start;
}
}
}
else
{
lean_object* v___x_1453_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_a_1437_);
v___x_1453_ = v___x_1154_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1437_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_indent_1151_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_activeTags_1152_);
v___x_1453_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1453_);
v___x_1455_ = v___x_1148_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_tail_1146_);
v___x_1455_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; 
v___x_1456_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v___x_1455_);
v_x_1131_ = v___x_1456_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v_out_1462_; lean_object* v_tagStack_1463_; lean_object* v_column_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1487_; 
v_a_1460_ = lean_ctor_get(v_f_1150_, 0);
lean_inc(v_a_1460_);
v_a_1461_ = lean_ctor_get(v_f_1150_, 1);
lean_inc(v_a_1461_);
lean_dec_ref(v_f_1150_);
v_out_1462_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1463_ = lean_ctor_get(v___y_1132_, 1);
v_column_1464_ = lean_ctor_get(v___y_1132_, 2);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1466_ = v___y_1132_;
v_isShared_1467_ = v_isSharedCheck_1487_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_column_1464_);
lean_inc(v_tagStack_1463_);
lean_inc(v_out_1462_);
lean_dec(v___y_1132_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1487_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4___closed__0));
lean_inc(v_column_1464_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_column_1464_);
lean_ctor_set(v___x_1469_, 1, v_out_1462_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1460_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_tagStack_1463_);
lean_ctor_set(v___x_1148_, 0, v___x_1470_);
v___x_1472_ = v___x_1148_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_tagStack_1463_);
v___x_1472_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___x_1472_);
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1474_ = v___x_1466_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_column_1464_);
v___x_1474_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1475_ = lean_unsigned_to_nat(1u);
v___x_1476_ = lean_nat_add(v_activeTags_1152_, v___x_1475_);
lean_dec(v_activeTags_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 2, v___x_1476_);
lean_ctor_set(v___x_1154_, 0, v_a_1461_);
v___x_1478_ = v___x_1154_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1461_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_indent_1151_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_tail_1146_);
lean_ctor_set(v___x_1142_, 0, v___x_1478_);
v___x_1480_ = v___x_1142_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_tail_1146_);
v___x_1480_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v___x_1480_);
v_x_1131_ = v___x_1481_;
v___y_1132_ = v___x_1474_;
goto _start;
}
}
}
}
}
}
}
v___jp_1156_:
{
lean_object* v_out_1157_; lean_object* v_tagStack_1158_; lean_object* v_column_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1195_; 
v_out_1157_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1158_ = lean_ctor_get(v___y_1132_, 1);
v_column_1159_ = lean_ctor_get(v___y_1132_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1161_ = v___y_1132_;
v_isShared_1162_ = v_isSharedCheck_1195_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_column_1159_);
lean_inc(v_tagStack_1158_);
lean_inc(v_out_1157_);
lean_dec(v___y_1132_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1195_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
lean_inc(v_column_1159_);
v___x_1163_ = lean_nat_to_int(v_column_1159_);
v___x_1164_ = lean_int_dec_lt(v___x_1163_, v_indent_1151_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_out_x27_1172_; lean_object* v___x_1174_; 
lean_dec(v___x_1163_);
lean_dec(v_column_1159_);
v___x_1165_ = l_Int_toNat(v_indent_1151_);
lean_dec(v_indent_1151_);
v___x_1166_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1165_);
v___x_1167_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1165_, v___x_1166_);
v___x_1168_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1167_, v_out_1157_);
v___x_1169_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1158_);
v___x_1170_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1158_, v_tagStack_1158_, v_activeTags_1152_, v___x_1169_);
v___x_1171_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1158_);
lean_dec(v_tagStack_1158_);
v_out_x27_1172_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1168_, v___x_1170_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v___x_1165_);
lean_ctor_set(v___x_1161_, 1, v___x_1171_);
lean_ctor_set(v___x_1161_, 0, v_out_x27_1172_);
v___x_1174_ = v___x_1161_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_out_x27_1172_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v___x_1165_);
v___x_1174_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1175_;
v___y_1132_ = v___x_1174_;
goto _start;
}
}
else
{
lean_object* v___x_1178_; uint32_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_out_x27_1189_; lean_object* v___x_1191_; 
v___x_1178_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_1179_ = 32;
v___x_1180_ = lean_int_sub(v_indent_1151_, v___x_1163_);
lean_dec(v___x_1163_);
lean_dec(v_indent_1151_);
v___x_1181_ = l_Int_toNat(v___x_1180_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_string_pushn(v___x_1178_, v___x_1179_, v___x_1181_);
lean_inc_ref(v___x_1182_);
v___x_1183_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1182_, v_out_1157_);
v___x_1184_ = lean_string_length(v___x_1182_);
lean_dec_ref(v___x_1182_);
v___x_1185_ = lean_nat_add(v_column_1159_, v___x_1184_);
lean_dec(v_column_1159_);
v___x_1186_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1158_);
v___x_1187_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1158_, v_tagStack_1158_, v_activeTags_1152_, v___x_1186_);
v___x_1188_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1158_);
lean_dec(v_tagStack_1158_);
v_out_x27_1189_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1183_, v___x_1187_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v___x_1185_);
lean_ctor_set(v___x_1161_, 1, v___x_1188_);
lean_ctor_set(v___x_1161_, 0, v_out_x27_1189_);
v___x_1191_ = v___x_1161_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_out_x27_1189_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v___x_1185_);
v___x_1191_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1192_;
v___y_1132_ = v___x_1191_;
goto _start;
}
}
}
}
v___jp_1196_:
{
if (v___y_1197_ == 0)
{
goto v___jp_1156_;
}
else
{
lean_object* v_out_1198_; lean_object* v_tagStack_1199_; lean_object* v_column_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_indent_1151_);
v_out_1198_ = lean_ctor_get(v___y_1132_, 0);
v_tagStack_1199_ = lean_ctor_get(v___y_1132_, 1);
v_column_1200_ = lean_ctor_get(v___y_1132_, 2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___y_1132_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1202_ = v___y_1132_;
v_isShared_1203_ = v_isSharedCheck_1213_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_column_1200_);
lean_inc(v_tagStack_1199_);
lean_inc(v_out_1198_);
lean_dec(v___y_1132_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1213_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_out_x27_1207_; lean_object* v___x_1209_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1152_);
lean_inc(v_tagStack_1199_);
v___x_1205_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1199_, v_tagStack_1199_, v_activeTags_1152_, v___x_1204_);
v___x_1206_ = l_List_drop___redArg(v_activeTags_1152_, v_tagStack_1199_);
lean_dec(v_tagStack_1199_);
v_out_x27_1207_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1198_, v___x_1205_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1206_);
lean_ctor_set(v___x_1202_, 0, v_out_x27_1207_);
v___x_1209_ = v___x_1202_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_out_x27_1207_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_column_1200_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1144_, v_flb_1145_, v_tail_1140_, v_tail_1146_);
v_x_1131_ = v___x_1210_;
v___y_1132_ = v___x_1209_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object* v_w_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1493_, v_x_1494_, v___y_1495_);
lean_dec(v_w_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object* v_f_1497_, lean_object* v_w_1498_, lean_object* v_indent_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1501_ = lean_box(1);
v___x_1502_ = 0;
v___x_1503_ = lean_nat_to_int(v_indent_1499_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1505_, 0, v_f_1497_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v___x_1504_);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1508_, 0, v___x_1501_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*2, v___x_1502_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1506_);
v___x_1510_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1498_, v___x_1509_, v___y_1500_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object* v_f_1511_, lean_object* v_w_1512_, lean_object* v_indent_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1511_, v_w_1512_, v_indent_1513_, v___y_1514_);
lean_dec(v_w_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object* v_f_1520_, lean_object* v_indent_1521_, lean_object* v_w_1522_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_snd_1525_; lean_object* v_out_1526_; 
v___x_1523_ = ((lean_object*)(l_Lean_Widget_TaggedText_prettyTagged___closed__0));
v___x_1524_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1520_, v_w_1522_, v_indent_1521_, v___x_1523_);
v_snd_1525_ = lean_ctor_get(v___x_1524_, 1);
lean_inc(v_snd_1525_);
lean_dec_ref(v___x_1524_);
v_out_1526_ = lean_ctor_get(v_snd_1525_, 0);
lean_inc_ref(v_out_1526_);
lean_dec(v_snd_1525_);
return v_out_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object* v_f_1527_, lean_object* v_indent_1528_, lean_object* v_w_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_1527_, v_indent_1528_, v_w_1529_);
lean_dec(v_w_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_nat_to_int(v_a_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object* v_acc_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_array_get_size(v_a_1534_);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_nat_dec_eq(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText___closed__0, &l_Lean_Widget_instInhabitedTaggedText___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText___closed__0);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_sub(v___x_1535_, v___x_1539_);
v___x_1541_ = lean_array_get_borrowed(v___x_1538_, v_a_1534_, v___x_1540_);
switch(lean_obj_tag(v___x_1541_))
{
case 0:
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v___x_1540_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v___x_1543_ = lean_string_append(v_acc_1533_, v_a_1542_);
v___x_1544_ = lean_array_pop(v_a_1534_);
v_acc_1533_ = v___x_1543_;
v_a_1534_ = v___x_1544_;
goto _start;
}
case 1:
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v___x_1540_);
v_a_1546_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_a_1546_);
v___x_1547_ = lean_array_pop(v_a_1534_);
v___x_1548_ = l_Array_reverse___redArg(v_a_1546_);
v___x_1549_ = l_Array_append___redArg(v___x_1547_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v_a_1534_ = v___x_1549_;
goto _start;
}
default: 
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1541_, 1);
lean_inc_ref(v_a_1551_);
v___x_1552_ = lean_array_set(v_a_1534_, v___x_1540_, v_a_1551_);
lean_dec(v___x_1540_);
v_a_1534_ = v___x_1552_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_1534_);
return v_acc_1533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object* v_00_u03b1_1554_, lean_object* v_acc_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v_acc_1555_, v_a_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object* v_tt_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1559_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___closed__0));
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_mk_empty_array_with_capacity(v___x_1560_);
v___x_1562_ = lean_array_push(v___x_1561_, v_tt_1558_);
v___x_1563_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v___x_1559_, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object* v_00_u03b1_1564_, lean_object* v_tt_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1565_);
return v___x_1566_;
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

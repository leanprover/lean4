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
static const lean_string_object l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__1 = (const lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg();
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg(){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__1));
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v_res_67_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object* v_00_u03b1_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg(){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg___boxed(lean_object* v___dummy_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Widget_instInhabitedTaggedText___redArg();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText(lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed(lean_object* v_inst_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_77_, v_x_78_, v_x_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq___redArg(lean_object* v_inst_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
switch(lean_obj_tag(v_x_83_))
{
case 0:
{
lean_dec_ref(v_inst_82_);
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v_a_86_; uint8_t v___x_87_; 
v_a_85_ = lean_ctor_get(v_x_83_, 0);
lean_inc_ref(v_a_85_);
lean_dec_ref_known(v_x_83_, 1);
v_a_86_ = lean_ctor_get(v_x_84_, 0);
lean_inc_ref(v_a_86_);
lean_dec_ref_known(v_x_84_, 1);
v___x_87_ = lean_string_dec_eq(v_a_85_, v_a_86_);
lean_dec_ref(v_a_86_);
lean_dec_ref(v_a_85_);
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
lean_dec_ref_known(v_x_83_, 1);
lean_dec_ref(v_x_84_);
v___x_88_ = 0;
return v___x_88_;
}
}
case 1:
{
if (lean_obj_tag(v_x_84_) == 1)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_a_89_ = lean_ctor_get(v_x_83_, 0);
lean_inc_ref(v_a_89_);
lean_dec_ref_known(v_x_83_, 1);
v_a_90_ = lean_ctor_get(v_x_84_, 0);
lean_inc_ref(v_a_90_);
lean_dec_ref_known(v_x_84_, 1);
v___x_91_ = lean_array_get_size(v_a_89_);
v___x_92_ = lean_array_get_size(v_a_90_);
v___x_93_ = lean_nat_dec_eq(v___x_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_dec_ref(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec_ref(v_inst_82_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_94_, 0, v_inst_82_);
v___x_95_ = l_Array_isEqvAux___redArg(v_a_89_, v_a_90_, v___x_94_, v___x_91_);
lean_dec_ref(v_a_90_);
lean_dec_ref(v_a_89_);
return v___x_95_;
}
}
else
{
uint8_t v___x_96_; 
lean_dec_ref_known(v_x_83_, 1);
lean_dec_ref(v_x_84_);
lean_dec_ref(v_inst_82_);
v___x_96_ = 0;
return v___x_96_;
}
}
default: 
{
if (lean_obj_tag(v_x_84_) == 2)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_a_97_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v_x_83_, 1);
lean_inc_ref(v_a_98_);
lean_dec_ref_known(v_x_83_, 2);
v_a_99_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_a_99_);
v_a_100_ = lean_ctor_get(v_x_84_, 1);
lean_inc_ref(v_a_100_);
lean_dec_ref_known(v_x_84_, 2);
lean_inc_ref(v_inst_82_);
v___x_101_ = lean_apply_2(v_inst_82_, v_a_97_, v_a_99_);
v___x_102_ = lean_unbox(v___x_101_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; 
lean_dec_ref(v_a_100_);
lean_dec_ref(v_a_98_);
lean_dec_ref(v_inst_82_);
v___x_103_ = lean_unbox(v___x_101_);
return v___x_103_;
}
else
{
v_x_83_ = v_a_98_;
v_x_84_ = v_a_100_;
goto _start;
}
}
else
{
uint8_t v___x_105_; 
lean_dec_ref_known(v_x_83_, 2);
lean_dec_ref(v_x_84_);
lean_dec_ref(v_inst_82_);
v___x_105_ = 0;
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_107_, v_x_108_, v_x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___boxed(lean_object* v_00_u03b1_111_, lean_object* v_inst_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lean_Widget_instBEqTaggedText_beq(v_00_u03b1_111_, v_inst_112_, v_x_113_, v_x_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText___redArg(lean_object* v_inst_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_118_, 0, lean_box(0));
lean_closure_set(v___x_118_, 1, v_inst_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText(lean_object* v_00_u03b1_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_121_, 0, lean_box(0));
lean_closure_set(v___x_121_, 1, v_inst_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(lean_object* v_inst_144_, lean_object* v_x_145_, lean_object* v_prec_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_144_, v_x_145_, v_prec_146_);
lean_dec(v_prec_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg(lean_object* v_inst_148_, lean_object* v_x_149_, lean_object* v_prec_150_){
_start:
{
switch(lean_obj_tag(v_x_149_))
{
case 0:
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v_inst_148_);
v_a_151_ = lean_ctor_get(v_x_149_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_171_ == 0)
{
v___x_153_ = v_x_149_;
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v_x_149_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___y_156_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(1024u);
v___x_168_ = lean_nat_dec_le(v___x_167_, v_prec_150_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_156_ = v___x_169_;
goto v___jp_155_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_157_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2));
v___x_158_ = l_String_quote(v_a_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 3);
lean_ctor_set(v___x_153_, 0, v___x_158_);
v___x_160_ = v___x_153_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_166_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
lean_inc(v___y_156_);
v___x_162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_162_, 0, v___y_156_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = 0;
v___x_164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*1, v___x_163_);
v___x_165_ = l_Repr_addAppParen(v___x_164_, v_prec_150_);
return v___x_165_;
}
}
}
}
case 1:
{
lean_object* v_a_172_; lean_object* v_localinst_173_; lean_object* v___y_175_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_a_172_ = lean_ctor_get(v_x_149_, 0);
lean_inc_ref(v_a_172_);
lean_dec_ref_known(v_x_149_, 1);
v_localinst_173_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_173_, 0, v_inst_148_);
v___x_183_ = lean_unsigned_to_nat(1024u);
v___x_184_ = lean_nat_dec_le(v___x_183_, v_prec_150_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_175_ = v___x_185_;
goto v___jp_174_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_175_ = v___x_186_;
goto v___jp_174_;
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_176_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7));
v___x_177_ = l_Array_repr___redArg(v_localinst_173_, v_a_172_);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
lean_inc(v___y_175_);
v___x_179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_179_, 0, v___y_175_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
v___x_182_ = l_Repr_addAppParen(v___x_181_, v_prec_150_);
return v___x_182_;
}
}
default: 
{
lean_object* v_a_187_; lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_211_; 
v_a_187_ = lean_ctor_get(v_x_149_, 0);
v_a_188_ = lean_ctor_get(v_x_149_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_211_ == 0)
{
v___x_190_ = v_x_149_;
v_isShared_191_ = v_isSharedCheck_211_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_inc(v_a_187_);
lean_dec(v_x_149_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_211_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___y_194_; uint8_t v___x_208_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_208_ = lean_nat_dec_le(v___x_192_, v_prec_150_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_194_ = v___x_209_;
goto v___jp_193_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_194_ = v___x_210_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_195_ = lean_box(1);
v___x_196_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10));
lean_inc_ref(v_inst_148_);
v___x_197_ = lean_apply_2(v_inst_148_, v_a_187_, v___x_192_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 5);
lean_ctor_set(v___x_190_, 1, v___x_197_);
lean_ctor_set(v___x_190_, 0, v___x_196_);
v___x_199_ = v___x_190_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_197_);
v___x_199_ = v_reuseFailAlloc_207_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_195_);
v___x_201_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_148_, v_a_188_, v___x_192_);
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_inc(v___y_194_);
v___x_203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_203_, 0, v___y_194_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = 0;
v___x_205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_204_);
v___x_206_ = l_Repr_addAppParen(v___x_205_, v_prec_150_);
return v___x_206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_x_214_, lean_object* v_prec_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_213_, v_x_214_, v_prec_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___boxed(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_x_219_, lean_object* v_prec_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Widget_instReprTaggedText_repr(v_00_u03b1_217_, v_inst_218_, v_x_219_, v_prec_220_);
lean_dec(v_prec_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText___redArg(lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, v_inst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, v_inst_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(lean_object* v_inst_236_, lean_object* v_json_237_){
_start:
{
lean_object* v___x_238_; 
lean_inc(v_json_237_);
v___x_238_ = l_Lean_Json_getTag_x3f(v_json_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; 
lean_dec(v_json_237_);
lean_dec_ref(v_inst_236_);
v___x_239_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1));
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_357_; 
v_val_240_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_357_ == 0)
{
v___x_242_ = v___x_238_;
v_isShared_243_ = v_isSharedCheck_357_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v___x_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_357_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_box(0);
v___x_245_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_246_ = lean_string_dec_eq(v_val_240_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
v___x_248_ = lean_string_dec_eq(v_val_240_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
lean_del_object(v___x_242_);
v___x_249_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
v___x_250_ = lean_string_dec_eq(v_val_240_, v___x_249_);
lean_dec(v_val_240_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec(v_json_237_);
lean_dec_ref(v_inst_236_);
v___x_251_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6));
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(2u);
v___x_253_ = lean_box(0);
v___x_254_ = l_Lean_Json_parseCtorFields(v_json_237_, v___x_249_, v___x_252_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_inst_236_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_254_, 1);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_array_get_borrowed(v___x_244_, v_a_263_, v___x_264_);
lean_inc_ref(v_inst_236_);
lean_inc(v___x_265_);
v___x_266_ = lean_apply_1(v_inst_236_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_a_263_);
lean_dec_ref(v_inst_236_);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_275_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_266_, 1);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_array_get(v___x_244_, v_a_263_, v___x_276_);
lean_dec(v_a_263_);
v___x_278_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_236_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_dec(v_a_275_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_283_, 0, v_a_275_);
lean_ctor_set(v___x_283_, 1, v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_val_240_);
lean_dec_ref(v_inst_236_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_box(0);
v___x_290_ = l_Lean_Json_parseCtorFields(v_json_237_, v___x_247_, v___x_288_, v___x_289_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_del_object(v___x_242_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_299_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_290_, 1);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_array_get(v___x_244_, v_a_299_, v___x_300_);
lean_dec(v_a_299_);
v___x_302_ = l_Lean_Json_getStr_x3f(v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_del_object(v___x_242_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_321_; 
v_a_311_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_321_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_321_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_302_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_321_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v_a_311_);
v___x_316_ = v___x_242_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_318_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_316_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_val_240_);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_box(0);
v___x_324_ = l_Lean_Json_parseCtorFields(v_json_237_, v___x_245_, v___x_322_, v___x_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_del_object(v___x_242_);
lean_dec_ref(v_inst_236_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v_localinst_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_333_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_324_, 1);
v_localinst_334_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg), 2, 1);
lean_closure_set(v_localinst_334_, 0, v_inst_236_);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_array_get(v___x_244_, v_a_333_, v___x_335_);
lean_dec(v_a_333_);
v___x_337_ = l_Lean_Array_fromJson_x3f___redArg(v_localinst_334_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_del_object(v___x_242_);
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_a_346_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_356_ == 0)
{
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v_a_346_);
v___x_351_ = v___x_242_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson(lean_object* v_00_u03b1_358_, lean_object* v_inst_359_, lean_object* v_json_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_359_, v_json_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText___redArg(lean_object* v_inst_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_363_, 0, lean_box(0));
lean_closure_set(v___x_363_, 1, v_inst_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_366_, 0, lean_box(0));
lean_closure_set(v___x_366_, 1, v_inst_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___redArg(lean_object* v_inst_367_, lean_object* v_x_368_){
_start:
{
switch(lean_obj_tag(v_x_368_))
{
case 0:
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_inst_367_);
v_a_369_ = lean_ctor_get(v_x_368_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_371_ = v_x_368_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v_x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 3);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_369_);
v___x_375_ = v_reuseFailAlloc_380_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_373_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = l_Lean_Json_mkObj(v___x_378_);
lean_dec_ref_known(v___x_378_, 2);
return v___x_379_;
}
}
}
case 1:
{
lean_object* v_a_382_; lean_object* v_localinst_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_a_382_ = lean_ctor_get(v_x_368_, 0);
lean_inc_ref(v_a_382_);
lean_dec_ref_known(v_x_368_, 1);
v_localinst_383_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson___redArg), 2, 1);
lean_closure_set(v_localinst_383_, 0, v_inst_367_);
v___x_384_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_385_ = l_Lean_Array_toJson___redArg(v_localinst_383_, v_a_382_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_Json_mkObj(v___x_388_);
lean_dec_ref_known(v___x_388_, 2);
return v___x_389_;
}
default: 
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_409_; 
v_a_390_ = lean_ctor_get(v_x_368_, 0);
v_a_391_ = lean_ctor_get(v_x_368_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_409_ == 0)
{
v___x_393_ = v_x_368_;
v_isShared_394_ = v_isSharedCheck_409_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_390_);
lean_dec(v_x_368_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_409_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_395_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
lean_inc_ref(v_inst_367_);
v___x_396_ = lean_apply_1(v_inst_367_, v_a_390_);
v___x_397_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_367_, v_a_391_);
v___x_398_ = lean_unsigned_to_nat(2u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_array_push(v___x_399_, v___x_396_);
v___x_401_ = lean_array_push(v___x_400_, v___x_397_);
v___x_402_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 0);
lean_ctor_set(v___x_393_, 1, v___x_402_);
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_404_ = v___x_393_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_402_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_Json_mkObj(v___x_406_);
lean_dec_ref_known(v___x_406_, 2);
return v___x_407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson(lean_object* v_00_u03b1_410_, lean_object* v_inst_411_, lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_411_, v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText___redArg(lean_object* v_inst_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_415_, 0, lean_box(0));
lean_closure_set(v___x_415_, 1, v_inst_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText(lean_object* v_00_u03b1_416_, lean_object* v_inst_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_418_, 0, lean_box(0));
lean_closure_set(v___x_418_, 1, v_inst_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText___redArg(lean_object* v_s_u2080_419_, lean_object* v_x_420_){
_start:
{
switch(lean_obj_tag(v_x_420_))
{
case 0:
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v_x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v_x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v_x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_string_append(v_a_421_, v_s_u2080_419_);
lean_dec_ref(v_s_u2080_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
case 1:
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_457_; 
v_a_430_ = lean_ctor_get(v_x_420_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_457_ == 0)
{
v___x_432_ = v_x_420_;
v_isShared_433_ = v_isSharedCheck_457_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v_x_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_457_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
v___x_435_ = lean_array_get_size(v_a_430_);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_sub(v___x_435_, v___x_436_);
v___x_438_ = lean_array_get(v___x_434_, v_a_430_, v___x_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_451_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_451_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = lean_string_append(v_a_439_, v_s_u2080_419_);
lean_dec_ref(v_s_u2080_419_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_450_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_array_set(v_a_430_, v___x_437_, v___x_445_);
lean_dec(v___x_437_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_446_);
v___x_448_ = v___x_432_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v___x_438_);
lean_dec(v___x_437_);
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 0);
lean_ctor_set(v___x_432_, 0, v_s_u2080_419_);
v___x_453_ = v___x_432_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_s_u2080_419_);
v___x_453_ = v_reuseFailAlloc_456_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_array_push(v_a_430_, v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
}
default: 
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_s_u2080_419_);
v___x_459_ = lean_unsigned_to_nat(2u);
v___x_460_ = lean_mk_empty_array_with_capacity(v___x_459_);
v___x_461_ = lean_array_push(v___x_460_, v_x_420_);
v___x_462_ = lean_array_push(v___x_461_, v___x_458_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText(lean_object* v_00_u03b1_464_, lean_object* v_s_u2080_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_u2080_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag___redArg(lean_object* v_acc_468_, lean_object* v_t_u2080_469_, lean_object* v_a_u2080_470_){
_start:
{
lean_object* v_a_472_; 
switch(lean_obj_tag(v_acc_468_))
{
case 1:
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_488_; 
v_a_479_ = lean_ctor_get(v_acc_468_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_acc_468_);
if (v_isSharedCheck_488_ == 0)
{
v___x_481_ = v_acc_468_;
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v_acc_468_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v_t_u2080_469_);
lean_ctor_set(v___x_483_, 1, v_a_u2080_470_);
v___x_484_ = lean_array_push(v_a_479_, v___x_483_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
case 0:
{
lean_object* v_a_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_a_489_ = lean_ctor_get(v_acc_468_, 0);
v___x_490_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_491_ = lean_string_dec_eq(v_a_489_, v___x_490_);
if (v___x_491_ == 0)
{
v_a_472_ = v_acc_468_;
goto v___jp_471_;
}
else
{
lean_object* v___x_492_; 
lean_dec_ref_known(v_acc_468_, 1);
v___x_492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_492_, 0, v_t_u2080_469_);
lean_ctor_set(v___x_492_, 1, v_a_u2080_470_);
return v___x_492_;
}
}
default: 
{
v_a_472_ = v_acc_468_;
goto v___jp_471_;
}
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_473_, 0, v_t_u2080_469_);
lean_ctor_set(v___x_473_, 1, v_a_u2080_470_);
v___x_474_ = lean_unsigned_to_nat(2u);
v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_476_ = lean_array_push(v___x_475_, v_a_472_);
v___x_477_ = lean_array_push(v___x_476_, v___x_473_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag(lean_object* v_00_u03b1_493_, lean_object* v_acc_494_, lean_object* v_t_u2080_495_, lean_object* v_a_u2080_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_acc_494_, v_t_u2080_495_, v_a_u2080_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(lean_object* v_f_498_, size_t v_sz_499_, size_t v_i_500_, lean_object* v_bs_501_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_lt(v_i_500_, v_sz_499_);
if (v___x_502_ == 0)
{
lean_dec(v_f_498_);
return v_bs_501_;
}
else
{
lean_object* v_v_503_; lean_object* v___x_504_; lean_object* v_bs_x27_505_; lean_object* v___x_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_v_503_ = lean_array_uget(v_bs_501_, v_i_500_);
v___x_504_ = lean_unsigned_to_nat(0u);
v_bs_x27_505_ = lean_array_uset(v_bs_501_, v_i_500_, v___x_504_);
lean_inc(v_f_498_);
v___x_506_ = l_Lean_Widget_TaggedText_map___redArg(v_f_498_, v_v_503_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_500_, v___x_507_);
v___x_509_ = lean_array_uset(v_bs_x27_505_, v_i_500_, v___x_506_);
v_i_500_ = v___x_508_;
v_bs_501_ = v___x_509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map___redArg(lean_object* v_f_511_, lean_object* v_x_512_){
_start:
{
switch(lean_obj_tag(v_x_512_))
{
case 0:
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_f_511_);
v_a_513_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v_x_512_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
case 1:
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_531_; 
v_a_521_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_531_ == 0)
{
v___x_523_ = v_x_512_;
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v_x_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
size_t v_sz_525_; size_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v_sz_525_ = lean_array_size(v_a_521_);
v___x_526_ = ((size_t)0ULL);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_511_, v_sz_525_, v___x_526_, v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_527_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
default: 
{
lean_object* v_a_532_; lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
v_a_532_ = lean_ctor_get(v_x_512_, 0);
v_a_533_ = lean_ctor_get(v_x_512_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v_x_512_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_inc(v_a_532_);
lean_dec(v_x_512_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
lean_inc(v_f_511_);
v___x_537_ = lean_apply_1(v_f_511_, v_a_532_);
v___x_538_ = l_Lean_Widget_TaggedText_map___redArg(v_f_511_, v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_538_);
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg___boxed(lean_object* v_f_543_, lean_object* v_sz_544_, lean_object* v_i_545_, lean_object* v_bs_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_544_);
lean_dec(v_sz_544_);
v_i_boxed_548_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_543_, v_sz_boxed_547_, v_i_boxed_548_, v_bs_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_f_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Widget_TaggedText_map___redArg(v_f_552_, v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_f_557_, size_t v_sz_558_, size_t v_i_559_, lean_object* v_bs_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_557_, v_sz_558_, v_i_559_, v_bs_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(lean_object* v_00_u03b1_562_, lean_object* v_00_u03b2_563_, lean_object* v_f_564_, lean_object* v_sz_565_, lean_object* v_i_566_, lean_object* v_bs_567_){
_start:
{
size_t v_sz_boxed_568_; size_t v_i_boxed_569_; lean_object* v_res_570_; 
v_sz_boxed_568_ = lean_unbox_usize(v_sz_565_);
lean_dec(v_sz_565_);
v_i_boxed_569_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(v_00_u03b1_562_, v_00_u03b2_563_, v_f_564_, v_sz_boxed_568_, v_i_boxed_569_, v_bs_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__0(lean_object* v_toPure_571_, lean_object* v_____do__lift_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_____do__lift_572_);
v___x_574_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__1(lean_object* v_____do__lift_575_, lean_object* v_toPure_576_, lean_object* v_____do__lift_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v_____do__lift_575_);
lean_ctor_set(v___x_578_, 1, v_____do__lift_577_);
v___x_579_ = lean_apply_2(v_toPure_576_, lean_box(0), v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object* v_inst_580_, lean_object* v_f_581_, lean_object* v_x_582_){
_start:
{
switch(lean_obj_tag(v_x_582_))
{
case 0:
{
lean_object* v_toApplicative_583_; lean_object* v_toPure_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_toApplicative_583_ = lean_ctor_get(v_inst_580_, 0);
lean_inc_ref(v_toApplicative_583_);
lean_dec(v_f_581_);
lean_dec_ref(v_inst_580_);
v_toPure_584_ = lean_ctor_get(v_toApplicative_583_, 1);
lean_inc(v_toPure_584_);
lean_dec_ref(v_toApplicative_583_);
v_a_585_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_593_ == 0)
{
v___x_587_ = v_x_582_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v_x_582_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_592_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = lean_apply_2(v_toPure_584_, lean_box(0), v___x_590_);
return v___x_591_;
}
}
}
case 1:
{
lean_object* v_toApplicative_594_; lean_object* v_toBind_595_; lean_object* v_toPure_596_; lean_object* v_a_597_; lean_object* v___f_598_; lean_object* v___x_599_; size_t v_sz_600_; size_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_toApplicative_594_ = lean_ctor_get(v_inst_580_, 0);
v_toBind_595_ = lean_ctor_get(v_inst_580_, 1);
lean_inc(v_toBind_595_);
v_toPure_596_ = lean_ctor_get(v_toApplicative_594_, 1);
v_a_597_ = lean_ctor_get(v_x_582_, 0);
lean_inc_ref(v_a_597_);
lean_dec_ref_known(v_x_582_, 1);
lean_inc(v_toPure_596_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_598_, 0, v_toPure_596_);
lean_inc_ref(v_inst_580_);
v___x_599_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg), 3, 2);
lean_closure_set(v___x_599_, 0, v_inst_580_);
lean_closure_set(v___x_599_, 1, v_f_581_);
v_sz_600_ = lean_array_size(v_a_597_);
v___x_601_ = ((size_t)0ULL);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_580_, v___x_599_, v_sz_600_, v___x_601_, v_a_597_);
v___x_603_ = lean_apply_4(v_toBind_595_, lean_box(0), lean_box(0), v___x_602_, v___f_598_);
return v___x_603_;
}
default: 
{
lean_object* v_toApplicative_604_; lean_object* v_toBind_605_; lean_object* v_toPure_606_; lean_object* v_a_607_; lean_object* v_a_608_; lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_toApplicative_604_ = lean_ctor_get(v_inst_580_, 0);
v_toBind_605_ = lean_ctor_get(v_inst_580_, 1);
lean_inc_n(v_toBind_605_, 2);
v_toPure_606_ = lean_ctor_get(v_toApplicative_604_, 1);
lean_inc(v_toPure_606_);
v_a_607_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_a_607_);
v_a_608_ = lean_ctor_get(v_x_582_, 1);
lean_inc_ref(v_a_608_);
lean_dec_ref_known(v_x_582_, 2);
lean_inc(v_f_581_);
v___f_609_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_609_, 0, v_toPure_606_);
lean_closure_set(v___f_609_, 1, v_inst_580_);
lean_closure_set(v___f_609_, 2, v_f_581_);
lean_closure_set(v___f_609_, 3, v_a_608_);
lean_closure_set(v___f_609_, 4, v_toBind_605_);
v___x_610_ = lean_apply_1(v_f_581_, v_a_607_);
v___x_611_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_610_, v___f_609_);
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__2(lean_object* v_toPure_612_, lean_object* v_inst_613_, lean_object* v_f_614_, lean_object* v_a_615_, lean_object* v_toBind_616_, lean_object* v_____do__lift_617_){
_start:
{
lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___f_618_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_618_, 0, v_____do__lift_617_);
lean_closure_set(v___f_618_, 1, v_toPure_612_);
v___x_619_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_613_, v_f_614_, v_a_615_);
v___x_620_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_619_, v___f_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM(lean_object* v_m_621_, lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_inst_624_, lean_object* v_f_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_624_, v_f_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__1(lean_object* v_inst_628_, lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v_____r_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_628_, v_f_629_, v_a_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg(lean_object* v_inst_633_, lean_object* v_f_634_, lean_object* v_x_635_){
_start:
{
switch(lean_obj_tag(v_x_635_))
{
case 0:
{
lean_object* v_toApplicative_636_; lean_object* v_toPure_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_toApplicative_636_ = lean_ctor_get(v_inst_633_, 0);
lean_inc_ref(v_toApplicative_636_);
lean_dec_ref_known(v_x_635_, 1);
lean_dec(v_f_634_);
lean_dec_ref(v_inst_633_);
v_toPure_637_ = lean_ctor_get(v_toApplicative_636_, 1);
lean_inc(v_toPure_637_);
lean_dec_ref(v_toApplicative_636_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_638_);
return v___x_639_;
}
case 1:
{
lean_object* v_toApplicative_640_; lean_object* v_toPure_641_; lean_object* v_a_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_toApplicative_640_ = lean_ctor_get(v_inst_633_, 0);
v_toPure_641_ = lean_ctor_get(v_toApplicative_640_, 1);
v_a_642_ = lean_ctor_get(v_x_635_, 0);
lean_inc_ref(v_a_642_);
lean_dec_ref_known(v_x_635_, 1);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_array_get_size(v_a_642_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_inc(v_toPure_641_);
lean_dec_ref(v_a_642_);
lean_dec(v_f_634_);
lean_dec_ref(v_inst_633_);
v___x_647_ = lean_apply_2(v_toPure_641_, lean_box(0), v___x_645_);
return v___x_647_;
}
else
{
lean_object* v___f_648_; uint8_t v___x_649_; 
lean_inc_ref(v_inst_633_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_648_, 0, v_inst_633_);
lean_closure_set(v___f_648_, 1, v_f_634_);
v___x_649_ = lean_nat_dec_le(v___x_644_, v___x_644_);
if (v___x_649_ == 0)
{
if (v___x_646_ == 0)
{
lean_object* v___x_650_; 
lean_inc(v_toPure_641_);
lean_dec_ref(v___f_648_);
lean_dec_ref(v_a_642_);
lean_dec_ref(v_inst_633_);
v___x_650_ = lean_apply_2(v_toPure_641_, lean_box(0), v___x_645_);
return v___x_650_;
}
else
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_644_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_633_, v___f_648_, v_a_642_, v___x_651_, v___x_652_, v___x_645_);
return v___x_653_;
}
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_644_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_633_, v___f_648_, v_a_642_, v___x_654_, v___x_655_, v___x_645_);
return v___x_656_;
}
}
}
default: 
{
lean_object* v_toBind_657_; lean_object* v_a_658_; lean_object* v_a_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_toBind_657_ = lean_ctor_get(v_inst_633_, 1);
lean_inc(v_toBind_657_);
v_a_658_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_a_658_);
v_a_659_ = lean_ctor_get(v_x_635_, 1);
lean_inc_ref_n(v_a_659_, 2);
lean_dec_ref_known(v_x_635_, 2);
lean_inc(v_f_634_);
v___f_660_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_660_, 0, v_inst_633_);
lean_closure_set(v___f_660_, 1, v_f_634_);
lean_closure_set(v___f_660_, 2, v_a_659_);
v___x_661_ = lean_apply_2(v_f_634_, v_a_658_, v_a_659_);
v___x_662_ = lean_apply_4(v_toBind_657_, lean_box(0), lean_box(0), v___x_661_, v___f_660_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__0(lean_object* v_inst_663_, lean_object* v_f_664_, lean_object* v_x_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_663_, v_f_664_, v___y_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM(lean_object* v_m_668_, lean_object* v_00_u03b1_669_, lean_object* v_inst_670_, lean_object* v_f_671_, lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_670_, v_f_671_, v_x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(lean_object* v_f_674_, size_t v_sz_675_, size_t v_i_676_, lean_object* v_bs_677_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
if (v___x_678_ == 0)
{
lean_dec_ref(v_f_674_);
return v_bs_677_;
}
else
{
lean_object* v_v_679_; lean_object* v___x_680_; lean_object* v_bs_x27_681_; lean_object* v___x_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v_v_679_ = lean_array_uget(v_bs_677_, v_i_676_);
v___x_680_ = lean_unsigned_to_nat(0u);
v_bs_x27_681_ = lean_array_uset(v_bs_677_, v_i_676_, v___x_680_);
lean_inc_ref(v_f_674_);
v___x_682_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_674_, v_v_679_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_676_, v___x_683_);
v___x_685_ = lean_array_uset(v_bs_x27_681_, v_i_676_, v___x_682_);
v_i_676_ = v___x_684_;
v_bs_677_ = v___x_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object* v_f_687_, lean_object* v_x_688_){
_start:
{
switch(lean_obj_tag(v_x_688_))
{
case 0:
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_f_687_);
v_a_689_ = lean_ctor_get(v_x_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v_x_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v_x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
case 1:
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_707_; 
v_a_697_ = lean_ctor_get(v_x_688_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_688_);
if (v_isSharedCheck_707_ == 0)
{
v___x_699_ = v_x_688_;
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v_x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
size_t v_sz_701_; size_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v_sz_701_ = lean_array_size(v_a_697_);
v___x_702_ = ((size_t)0ULL);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_687_, v_sz_701_, v___x_702_, v_a_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_703_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
default: 
{
lean_object* v_a_708_; lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_708_ = lean_ctor_get(v_x_688_, 0);
lean_inc(v_a_708_);
v_a_709_ = lean_ctor_get(v_x_688_, 1);
lean_inc_ref(v_a_709_);
lean_dec_ref_known(v_x_688_, 2);
v___x_710_ = lean_apply_2(v_f_687_, v_a_708_, v_a_709_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg___boxed(lean_object* v_f_711_, lean_object* v_sz_712_, lean_object* v_i_713_, lean_object* v_bs_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_712_);
lean_dec(v_sz_712_);
v_i_boxed_716_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_711_, v_sz_boxed_715_, v_i_boxed_716_, v_bs_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_f_720_, lean_object* v_x_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_720_, v_x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_f_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_bs_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_725_, v_sz_726_, v_i_727_, v_bs_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_f_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_bs_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_737_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(v_00_u03b1_730_, v_00_u03b2_731_, v_f_732_, v_sz_boxed_736_, v_i_boxed_737_, v_bs_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___redArg(lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_x_741_){
_start:
{
switch(lean_obj_tag(v_x_741_))
{
case 0:
{
lean_object* v_toApplicative_742_; lean_object* v_toPure_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_toApplicative_742_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_742_);
lean_dec(v_f_740_);
lean_dec_ref(v_inst_739_);
v_toPure_743_ = lean_ctor_get(v_toApplicative_742_, 1);
lean_inc(v_toPure_743_);
lean_dec_ref(v_toApplicative_742_);
v_a_744_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v_x_741_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v_x_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_apply_2(v_toPure_743_, lean_box(0), v___x_749_);
return v___x_750_;
}
}
}
case 1:
{
lean_object* v_toApplicative_753_; lean_object* v_toBind_754_; lean_object* v_toPure_755_; lean_object* v_a_756_; lean_object* v___f_757_; lean_object* v___x_758_; size_t v_sz_759_; size_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_toApplicative_753_ = lean_ctor_get(v_inst_739_, 0);
v_toBind_754_ = lean_ctor_get(v_inst_739_, 1);
lean_inc(v_toBind_754_);
v_toPure_755_ = lean_ctor_get(v_toApplicative_753_, 1);
v_a_756_ = lean_ctor_get(v_x_741_, 0);
lean_inc_ref(v_a_756_);
lean_dec_ref_known(v_x_741_, 1);
lean_inc(v_toPure_755_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_757_, 0, v_toPure_755_);
lean_inc_ref(v_inst_739_);
v___x_758_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_rewriteM___redArg), 3, 2);
lean_closure_set(v___x_758_, 0, v_inst_739_);
lean_closure_set(v___x_758_, 1, v_f_740_);
v_sz_759_ = lean_array_size(v_a_756_);
v___x_760_ = ((size_t)0ULL);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___x_758_, v_sz_759_, v___x_760_, v_a_756_);
v___x_762_ = lean_apply_4(v_toBind_754_, lean_box(0), lean_box(0), v___x_761_, v___f_757_);
return v___x_762_;
}
default: 
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_765_; 
lean_dec_ref(v_inst_739_);
v_a_763_ = lean_ctor_get(v_x_741_, 0);
lean_inc(v_a_763_);
v_a_764_ = lean_ctor_get(v_x_741_, 1);
lean_inc_ref(v_a_764_);
lean_dec_ref_known(v_x_741_, 2);
v___x_765_ = lean_apply_2(v_f_740_, v_a_763_, v_a_764_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM(lean_object* v_m_766_, lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_inst_769_, lean_object* v_f_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Widget_TaggedText_rewriteM___redArg(v_inst_769_, v_f_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(lean_object* v_inst_773_, lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v_a_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_rpcEncode_778_; lean_object* v___x_648__overap_779_; lean_object* v___x_780_; lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
v_rpcEncode_778_ = lean_ctor_get(v_inst_773_, 0);
lean_inc_ref(v_rpcEncode_778_);
lean_dec_ref(v_inst_773_);
v___x_648__overap_779_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_774_, v_rpcEncode_778_, v_a_776_);
v___x_780_ = lean_apply_1(v___x_648__overap_779_, v___y_777_);
v_fst_781_ = lean_ctor_get(v___x_780_, 0);
v_snd_782_ = lean_ctor_get(v___x_780_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v___x_780_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_snd_782_);
lean_inc(v_fst_781_);
lean_dec(v___x_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v___x_775_, v_fst_781_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_snd_782_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(lean_object* v___f_791_, lean_object* v_inst_792_, lean_object* v___x_793_, lean_object* v_a_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v___f_791_, v_a_794_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v___x_793_);
lean_dec_ref(v_inst_792_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
else
{
lean_object* v_a_805_; lean_object* v_rpcDecode_806_; lean_object* v___x_661__overap_807_; lean_object* v___x_808_; 
v_a_805_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_796_, 1);
v_rpcDecode_806_ = lean_ctor_get(v_inst_792_, 1);
lean_inc_ref(v_rpcDecode_806_);
lean_dec_ref(v_inst_792_);
v___x_661__overap_807_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_793_, v_rpcDecode_806_, v_a_805_);
lean_inc_ref(v___y_795_);
v___x_808_ = lean_apply_1(v___x_661__overap_807_, v___y_795_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed(lean_object* v___f_809_, lean_object* v_inst_810_, lean_object* v___x_811_, lean_object* v_a_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(v___f_809_, v_inst_810_, v___x_811_, v_a_812_, v___y_813_);
lean_dec_ref(v___y_813_);
return v_res_814_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9));
v___x_862_ = l_ReaderT_instMonad___redArg(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22(void){
_start:
{
lean_object* v___x_863_; lean_object* v___f_864_; 
v___x_863_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_864_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_864_, 0, v___x_863_);
return v___f_864_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23(void){
_start:
{
lean_object* v___x_865_; lean_object* v___f_866_; 
v___x_865_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_866_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_866_, 0, v___x_865_);
return v___f_866_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24(void){
_start:
{
lean_object* v___x_867_; lean_object* v___f_868_; 
v___x_867_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_868_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_868_, 0, v___x_867_);
return v___f_868_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25(void){
_start:
{
lean_object* v___x_869_; lean_object* v___f_870_; 
v___x_869_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_870_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_870_, 0, v___x_869_);
return v___f_870_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_872_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_872_, 0, lean_box(0));
lean_closure_set(v___x_872_, 1, lean_box(0));
lean_closure_set(v___x_872_, 2, v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27(void){
_start:
{
lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___f_873_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22);
v___x_874_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___f_873_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_877_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_877_, 0, lean_box(0));
lean_closure_set(v___x_877_, 1, lean_box(0));
lean_closure_set(v___x_877_, 2, v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29(void){
_start:
{
lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___f_878_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25);
v___f_879_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24);
v___f_880_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23);
v___x_881_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28);
v___x_882_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27);
v___x_883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_881_);
lean_ctor_set(v___x_883_, 2, v___f_880_);
lean_ctor_set(v___x_883_, 3, v___f_879_);
lean_ctor_set(v___x_883_, 4, v___f_878_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_885_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_885_, 0, lean_box(0));
lean_closure_set(v___x_885_, 1, lean_box(0));
lean_closure_set(v___x_885_, 2, v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30);
v___x_887_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg(lean_object* v_inst_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_897_; 
v___x_891_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_892_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20));
lean_inc_ref(v_inst_890_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0), 5, 3);
lean_closure_set(v___f_893_, 0, v_inst_890_);
lean_closure_set(v___f_893_, 1, v___x_891_);
lean_closure_set(v___f_893_, 2, v___x_892_);
v___x_894_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31);
v___f_895_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32));
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_896_, 0, v___f_895_);
lean_closure_set(v___f_896_, 1, v_inst_890_);
lean_closure_set(v___f_896_, 2, v___x_894_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___f_893_);
lean_ctor_set(v___x_897_, 1, v___f_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable(lean_object* v_00_u03b1_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object* v_s_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_out_911_; lean_object* v_tagStack_912_; lean_object* v_column_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_925_; 
v_out_911_ = lean_ctor_get(v___y_910_, 0);
v_tagStack_912_ = lean_ctor_get(v___y_910_, 1);
v_column_913_ = lean_ctor_get(v___y_910_, 2);
v_isSharedCheck_925_ = !lean_is_exclusive(v___y_910_);
if (v_isSharedCheck_925_ == 0)
{
v___x_915_ = v___y_910_;
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_column_913_);
lean_inc(v_tagStack_912_);
lean_inc(v_out_911_);
lean_dec(v___y_910_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_917_ = lean_box(0);
lean_inc_ref(v_s_909_);
v___x_918_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_909_, v_out_911_);
v___x_919_ = lean_string_length(v_s_909_);
lean_dec_ref(v_s_909_);
v___x_920_ = lean_nat_add(v_column_913_, v___x_919_);
lean_dec(v_column_913_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 2, v___x_920_);
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_922_ = v___x_915_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_tagStack_912_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_920_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_917_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t v___x_926_, lean_object* v_s_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_string_push(v_s_927_, v___x_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object* v___x_929_, lean_object* v_s_930_){
_start:
{
uint32_t v___x_832__boxed_931_; lean_object* v_res_932_; 
v___x_832__boxed_931_ = lean_unbox_uint32(v___x_929_);
lean_dec(v___x_929_);
v_res_932_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_832__boxed_931_, v_s_930_);
return v_res_932_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = 32;
v___x_935_ = lean_box_uint32(v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___f_937_; 
v___x_936_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
v___f_937_ = lean_alloc_closure((void*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed), 2, 1);
lean_closure_set(v___f_937_, 0, v___x_936_);
return v___f_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object* v_indent_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_out_940_; lean_object* v_tagStack_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_954_; 
v_out_940_ = lean_ctor_get(v___y_939_, 0);
v_tagStack_941_ = lean_ctor_get(v___y_939_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v___y_939_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v___y_939_, 2);
lean_dec(v_unused_955_);
v___x_943_ = v___y_939_;
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_tagStack_941_);
lean_inc(v_out_940_);
lean_dec(v___y_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_945_ = lean_box(0);
v___x_946_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
v___f_947_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
lean_inc(v_indent_938_);
v___x_948_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_947_, v_indent_938_, v___x_946_);
v___x_949_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_948_, v_out_940_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 2, v_indent_938_);
lean_ctor_set(v___x_943_, 0, v___x_949_);
v___x_951_ = v___x_943_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_tagStack_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_indent_938_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_945_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object* v_____do__lift_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_column_958_; lean_object* v___x_959_; 
v_column_958_ = lean_ctor_get(v_____do__lift_956_, 2);
lean_inc(v_column_958_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_column_958_);
lean_ctor_set(v___x_959_, 1, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object* v_____do__lift_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_960_, v___y_961_);
lean_dec_ref(v_____do__lift_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object* v_n_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_out_965_; lean_object* v_tagStack_966_; lean_object* v_column_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_980_; 
v_out_965_ = lean_ctor_get(v___y_964_, 0);
v_tagStack_966_ = lean_ctor_get(v___y_964_, 1);
v_column_967_ = lean_ctor_get(v___y_964_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v___y_964_);
if (v_isSharedCheck_980_ == 0)
{
v___x_969_ = v___y_964_;
v_isShared_970_ = v_isSharedCheck_980_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_column_967_);
lean_inc(v_tagStack_966_);
lean_inc(v_out_965_);
lean_dec(v___y_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_980_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_971_ = lean_box(0);
v___x_972_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_967_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_column_967_);
lean_ctor_set(v___x_973_, 1, v_out_965_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_n_963_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_tagStack_966_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_975_);
lean_ctor_set(v___x_969_, 0, v___x_972_);
v___x_977_ = v___x_969_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_column_967_);
v___x_977_ = v_reuseFailAlloc_979_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_971_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object* v_acc_981_, lean_object* v_x_982_){
_start:
{
lean_object* v_snd_983_; lean_object* v_fst_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_snd_983_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_snd_983_);
v_fst_984_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v_x_982_);
v_fst_985_ = lean_ctor_get(v_snd_983_, 0);
v_snd_986_ = lean_ctor_get(v_snd_983_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_snd_983_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v_snd_983_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_inc(v_fst_985_);
lean_dec(v_snd_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v_fst_985_);
lean_ctor_set(v___x_988_, 0, v_fst_984_);
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_fst_985_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_986_, v___x_991_, v_acc_981_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object* v___f_997_, lean_object* v_n_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_out_1000_; lean_object* v_tagStack_1001_; lean_object* v_column_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1015_; 
v_out_1000_ = lean_ctor_get(v___y_999_, 0);
v_tagStack_1001_ = lean_ctor_get(v___y_999_, 1);
v_column_1002_ = lean_ctor_get(v___y_999_, 2);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___y_999_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1004_ = v___y_999_;
v_isShared_1005_ = v_isSharedCheck_1015_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_column_1002_);
lean_inc(v_tagStack_1001_);
lean_inc(v_out_1000_);
lean_dec(v___y_999_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1015_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_out_x27_1010_; lean_object* v___x_1012_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_n_998_);
lean_inc(v_tagStack_1001_);
v___x_1008_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1001_, v_tagStack_1001_, v_n_998_, v___x_1007_);
v___x_1009_ = l_List_drop___redArg(v_n_998_, v_tagStack_1001_);
lean_dec(v_tagStack_1001_);
v_out_x27_1010_ = l_List_foldl___redArg(v___f_997_, v_out_1000_, v___x_1008_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1009_);
lean_ctor_set(v___x_1004_, 0, v_out_x27_1010_);
v___x_1012_ = v___x_1004_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_out_x27_1010_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_column_1002_);
v___x_1012_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1006_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v_zero_1038_; uint8_t v_isZero_1039_; 
v_zero_1038_ = lean_unsigned_to_nat(0u);
v_isZero_1039_ = lean_nat_dec_eq(v_x_1036_, v_zero_1038_);
if (v_isZero_1039_ == 1)
{
lean_dec(v_x_1036_);
return v_x_1037_;
}
else
{
uint32_t v___x_1040_; lean_object* v_one_1041_; lean_object* v_n_1042_; lean_object* v___x_1043_; 
v___x_1040_ = 32;
v_one_1041_ = lean_unsigned_to_nat(1u);
v_n_1042_ = lean_nat_sub(v_x_1036_, v_one_1041_);
lean_dec(v_x_1036_);
v___x_1043_ = lean_string_push(v_x_1037_, v___x_1040_);
v_x_1036_ = v_n_1042_;
v_x_1037_ = v___x_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object* v_fla_1045_, uint8_t v_flb_1046_, lean_object* v_tail_1047_, lean_object* v_is_x27_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1049_, 0, v_fla_1045_);
lean_ctor_set(v___x_1049_, 1, v_is_x27_1048_);
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*2, v_flb_1046_);
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_tail_1047_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object* v_fla_1051_, lean_object* v_flb_1052_, lean_object* v_tail_1053_, lean_object* v_is_x27_1054_){
_start:
{
uint8_t v_flb_6239__boxed_1055_; lean_object* v_res_1056_; 
v_flb_6239__boxed_1055_ = lean_unbox(v_flb_1052_);
v_res_1056_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1051_, v_flb_6239__boxed_1055_, v_tail_1053_, v_is_x27_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t v_flb_1057_, lean_object* v_items_1058_, lean_object* v_gs_1059_, lean_object* v_w_1060_, lean_object* v___y_1061_){
_start:
{
uint8_t v___y_1063_; lean_object* v_column_1068_; uint8_t v___x_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v_g_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_r_1076_; lean_object* v___y_1078_; uint8_t v_foundLine_1083_; lean_object* v_space_1084_; uint8_t v___x_1085_; 
v_column_1068_ = lean_ctor_get(v___y_1061_, 2);
v___x_1069_ = 0;
v___x_1070_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1057_, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1071_, 0, v___x_1070_);
lean_inc(v_items_1058_);
v_g_1072_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1072_, 0, v___x_1071_);
lean_ctor_set(v_g_1072_, 1, v_items_1058_);
lean_ctor_set_uint8(v_g_1072_, sizeof(void*)*2, v_flb_1057_);
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_g_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_nat_sub(v_w_1060_, v_column_1068_);
lean_inc(v___x_1075_);
lean_inc(v_column_1068_);
v_r_1076_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1074_, v_column_1068_, v___x_1075_);
v_foundLine_1083_ = lean_ctor_get_uint8(v_r_1076_, sizeof(void*)*1);
v_space_1084_ = lean_ctor_get(v_r_1076_, 0);
lean_inc(v_space_1084_);
v___x_1085_ = lean_nat_dec_lt(v___x_1075_, v_space_1084_);
if (v___x_1085_ == 0)
{
if (v_foundLine_1083_ == 0)
{
lean_object* v___x_1086_; lean_object* v_r_u2082_1087_; uint8_t v_foundLine_1088_; uint8_t v_foundFlattenedHardLine_1089_; lean_object* v_space_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v___x_1086_ = lean_nat_sub(v___x_1075_, v_space_1084_);
lean_inc(v_column_1068_);
lean_inc(v_gs_1059_);
v_r_u2082_1087_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1059_, v_column_1068_, v___x_1086_);
v_foundLine_1088_ = lean_ctor_get_uint8(v_r_u2082_1087_, sizeof(void*)*1);
v_foundFlattenedHardLine_1089_ = lean_ctor_get_uint8(v_r_u2082_1087_, sizeof(void*)*1 + 1);
v_space_1090_ = lean_ctor_get(v_r_u2082_1087_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_r_u2082_1087_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v_r_u2082_1087_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_space_1090_);
lean_dec(v_r_u2082_1087_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_nat_add(v_space_1084_, v_space_1090_);
lean_dec(v_space_1090_);
lean_dec(v_space_1084_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*1, v_foundLine_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1089_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v___y_1078_ = v___x_1096_;
goto v___jp_1077_;
}
}
}
else
{
lean_dec(v_space_1084_);
lean_inc_ref(v_r_1076_);
v___y_1078_ = v_r_1076_;
goto v___jp_1077_;
}
}
else
{
lean_dec(v_space_1084_);
lean_inc_ref(v_r_1076_);
v___y_1078_ = v_r_1076_;
goto v___jp_1077_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1064_, 0, v___y_1063_);
v___x_1065_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_items_1058_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*2, v_flb_1057_);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_gs_1059_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___y_1061_);
return v___x_1067_;
}
v___jp_1077_:
{
uint8_t v_foundFlattenedHardLine_1079_; 
v_foundFlattenedHardLine_1079_ = lean_ctor_get_uint8(v_r_1076_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1076_);
if (v_foundFlattenedHardLine_1079_ == 0)
{
lean_object* v_space_1080_; uint8_t v___x_1081_; 
v_space_1080_ = lean_ctor_get(v___y_1078_, 0);
lean_inc(v_space_1080_);
lean_dec_ref(v___y_1078_);
v___x_1081_ = lean_nat_dec_le(v_space_1080_, v___x_1075_);
lean_dec(v___x_1075_);
lean_dec(v_space_1080_);
v___y_1063_ = v___x_1081_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1082_; 
lean_dec_ref(v___y_1078_);
lean_dec(v___x_1075_);
v___x_1082_ = 0;
v___y_1063_ = v___x_1082_;
goto v___jp_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object* v_flb_1099_, lean_object* v_items_1100_, lean_object* v_gs_1101_, lean_object* v_w_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_flb_boxed_1104_; lean_object* v_res_1105_; 
v_flb_boxed_1104_ = lean_unbox(v_flb_1099_);
v_res_1105_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_1104_, v_items_1100_, v_gs_1101_, v_w_1102_, v___y_1103_);
lean_dec(v_w_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
return v_x_1106_;
}
else
{
lean_object* v_head_1108_; lean_object* v_snd_1109_; lean_object* v_tail_1110_; lean_object* v_fst_1111_; lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1122_; 
v_head_1108_ = lean_ctor_get(v_x_1107_, 0);
lean_inc(v_head_1108_);
v_snd_1109_ = lean_ctor_get(v_head_1108_, 1);
lean_inc(v_snd_1109_);
v_tail_1110_ = lean_ctor_get(v_x_1107_, 1);
lean_inc(v_tail_1110_);
lean_dec_ref_known(v_x_1107_, 2);
v_fst_1111_ = lean_ctor_get(v_head_1108_, 0);
lean_inc(v_fst_1111_);
lean_dec(v_head_1108_);
v_fst_1112_ = lean_ctor_get(v_snd_1109_, 0);
v_snd_1113_ = lean_ctor_get(v_snd_1109_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_snd_1109_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1115_ = v_snd_1109_;
v_isShared_1116_ = v_isSharedCheck_1122_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_snd_1113_);
lean_inc(v_fst_1112_);
lean_dec(v_snd_1109_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1122_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v_fst_1112_);
lean_ctor_set(v___x_1115_, 0, v_fst_1111_);
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_fst_1112_);
v___x_1118_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_1113_, v___x_1118_, v_x_1106_);
v_x_1106_ = v___x_1119_;
v_x_1107_ = v_tail_1110_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_1125_ = l_instInhabitedOfMonad___redArg(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object* v_msg_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_6144__overap_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_obj_once(&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0, &l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once, _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
v___x_6144__overap_1129_ = lean_panic_fn_borrowed(v___x_1128_, v_msg_1126_);
v___x_1130_ = lean_apply_1(v___x_6144__overap_1129_, v___y_1127_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1133_ = lean_string_length(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object* v_w_1135_, lean_object* v_x_1136_, lean_object* v___y_1137_){
_start:
{
if (lean_obj_tag(v_x_1136_) == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v___y_1137_);
return v___x_1139_;
}
else
{
lean_object* v_head_1140_; lean_object* v_items_1141_; 
v_head_1140_ = lean_ctor_get(v_x_1136_, 0);
v_items_1141_ = lean_ctor_get(v_head_1140_, 1);
lean_inc(v_items_1141_);
if (lean_obj_tag(v_items_1141_) == 0)
{
lean_object* v_tail_1142_; 
v_tail_1142_ = lean_ctor_get(v_x_1136_, 1);
lean_inc(v_tail_1142_);
lean_dec_ref_known(v_x_1136_, 2);
v_x_1136_ = v_tail_1142_;
goto _start;
}
else
{
lean_object* v_head_1144_; lean_object* v_tail_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1496_; 
lean_inc(v_head_1140_);
v_head_1144_ = lean_ctor_get(v_items_1141_, 0);
lean_inc(v_head_1144_);
v_tail_1145_ = lean_ctor_get(v_x_1136_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_x_1136_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_x_1136_, 0);
lean_dec(v_unused_1497_);
v___x_1147_ = v_x_1136_;
v_isShared_1148_ = v_isSharedCheck_1496_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_tail_1145_);
lean_dec(v_x_1136_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1496_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_fla_1149_; uint8_t v_flb_1150_; lean_object* v_tail_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1494_; 
v_fla_1149_ = lean_ctor_get(v_head_1140_, 0);
lean_inc(v_fla_1149_);
v_flb_1150_ = lean_ctor_get_uint8(v_head_1140_, sizeof(void*)*2);
lean_dec(v_head_1140_);
v_tail_1151_ = lean_ctor_get(v_items_1141_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_items_1141_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_items_1141_, 0);
lean_dec(v_unused_1495_);
v___x_1153_ = v_items_1141_;
v_isShared_1154_ = v_isSharedCheck_1494_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_tail_1151_);
lean_dec(v_items_1141_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1494_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_f_1155_; lean_object* v_indent_1156_; lean_object* v_activeTags_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1493_; 
v_f_1155_ = lean_ctor_get(v_head_1144_, 0);
v_indent_1156_ = lean_ctor_get(v_head_1144_, 1);
v_activeTags_1157_ = lean_ctor_get(v_head_1144_, 2);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_head_1144_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1159_ = v_head_1144_;
v_isShared_1160_ = v_isSharedCheck_1493_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_activeTags_1157_);
lean_inc(v_indent_1156_);
lean_inc(v_f_1155_);
lean_dec(v_head_1144_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1493_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___y_1202_; 
switch(lean_obj_tag(v_f_1155_))
{
case 0:
{
lean_object* v_out_1219_; lean_object* v_tagStack_1220_; lean_object* v_column_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1234_; 
lean_del_object(v___x_1159_);
lean_dec(v_indent_1156_);
lean_del_object(v___x_1153_);
lean_del_object(v___x_1147_);
v_out_1219_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1220_ = lean_ctor_get(v___y_1137_, 1);
v_column_1221_ = lean_ctor_get(v___y_1137_, 2);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1223_ = v___y_1137_;
v_isShared_1224_ = v_isSharedCheck_1234_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_column_1221_);
lean_inc(v_tagStack_1220_);
lean_inc(v_out_1219_);
lean_dec(v___y_1137_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1234_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_out_x27_1228_; lean_object* v___x_1230_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1220_);
v___x_1226_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1220_, v_tagStack_1220_, v_activeTags_1157_, v___x_1225_);
v___x_1227_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1220_);
lean_dec(v_tagStack_1220_);
v_out_x27_1228_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1219_, v___x_1226_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1227_);
lean_ctor_set(v___x_1223_, 0, v_out_x27_1228_);
v___x_1230_ = v___x_1223_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_out_x27_1228_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_column_1221_);
v___x_1230_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; 
v___x_1231_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1231_;
v___y_1137_ = v___x_1230_;
goto _start;
}
}
}
case 1:
{
lean_del_object(v___x_1159_);
lean_del_object(v___x_1153_);
lean_del_object(v___x_1147_);
if (v_flb_1150_ == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1149_);
if (v___x_1235_ == 0)
{
lean_object* v_out_1236_; lean_object* v_tagStack_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1254_; 
v_out_1236_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1237_ = lean_ctor_get(v___y_1137_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___y_1137_, 2);
lean_dec(v_unused_1255_);
v___x_1239_ = v___y_1137_;
v_isShared_1240_ = v_isSharedCheck_1254_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tagStack_1237_);
lean_inc(v_out_1236_);
lean_dec(v___y_1137_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1254_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_out_x27_1248_; lean_object* v___x_1250_; 
v___x_1241_ = l_Int_toNat(v_indent_1156_);
lean_dec(v_indent_1156_);
v___x_1242_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1241_);
v___x_1243_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1241_, v___x_1242_);
v___x_1244_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1243_, v_out_1236_);
v___x_1245_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1237_);
v___x_1246_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1237_, v_tagStack_1237_, v_activeTags_1157_, v___x_1245_);
v___x_1247_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1237_);
lean_dec(v_tagStack_1237_);
v_out_x27_1248_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1244_, v___x_1246_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 2, v___x_1241_);
lean_ctor_set(v___x_1239_, 1, v___x_1247_);
lean_ctor_set(v___x_1239_, 0, v_out_x27_1248_);
v___x_1250_ = v___x_1239_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_out_x27_1248_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v___x_1241_);
v___x_1250_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1251_;
v___y_1137_ = v___x_1250_;
goto _start;
}
}
}
else
{
lean_object* v_out_1256_; lean_object* v_tagStack_1257_; lean_object* v_column_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_indent_1156_);
v_out_1256_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1257_ = lean_ctor_get(v___y_1137_, 1);
v_column_1258_ = lean_ctor_get(v___y_1137_, 2);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1260_ = v___y_1137_;
v_isShared_1261_ = v_isSharedCheck_1275_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_column_1258_);
lean_inc(v_tagStack_1257_);
lean_inc(v_out_1256_);
lean_dec(v___y_1137_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1275_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_out_x27_1269_; lean_object* v___x_1271_; 
v___x_1262_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1263_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1262_, v_out_1256_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_column_1258_, v___x_1264_);
lean_dec(v_column_1258_);
v___x_1266_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1257_);
v___x_1267_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1257_, v_tagStack_1257_, v_activeTags_1157_, v___x_1266_);
v___x_1268_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1257_);
lean_dec(v_tagStack_1257_);
v_out_x27_1269_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1263_, v___x_1267_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 2, v___x_1265_);
lean_ctor_set(v___x_1260_, 1, v___x_1268_);
lean_ctor_set(v___x_1260_, 0, v_out_x27_1269_);
v___x_1271_ = v___x_1260_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_out_x27_1269_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___x_1265_);
v___x_1271_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1272_;
v___y_1137_ = v___x_1271_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = l_Int_toNat(v_indent_1156_);
lean_dec(v_indent_1156_);
v___x_1277_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1149_);
lean_dec(v_fla_1149_);
if (v___x_1277_ == 0)
{
lean_object* v_out_1278_; lean_object* v_tagStack_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1297_; 
v_out_1278_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1279_ = lean_ctor_get(v___y_1137_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v___y_1137_, 2);
lean_dec(v_unused_1298_);
v___x_1281_ = v___y_1137_;
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_tagStack_1279_);
lean_inc(v_out_1278_);
lean_dec(v___y_1137_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_out_x27_1289_; lean_object* v___x_1291_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1276_);
v___x_1284_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1276_, v___x_1283_);
v___x_1285_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1284_, v_out_1278_);
v___x_1286_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1279_);
v___x_1287_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1279_, v_tagStack_1279_, v_activeTags_1157_, v___x_1286_);
v___x_1288_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1279_);
lean_dec(v_tagStack_1279_);
v_out_x27_1289_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1285_, v___x_1287_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 2, v___x_1276_);
lean_ctor_set(v___x_1281_, 1, v___x_1288_);
lean_ctor_set(v___x_1281_, 0, v_out_x27_1289_);
v___x_1291_ = v___x_1281_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_out_x27_1289_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v___x_1276_);
v___x_1291_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; 
v___x_1292_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1150_, v_tail_1151_, v_tail_1145_, v_w_1135_, v___x_1291_);
v_fst_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_fst_1293_);
v_snd_1294_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_snd_1294_);
lean_dec_ref(v___x_1292_);
v_x_1136_ = v_fst_1293_;
v___y_1137_ = v_snd_1294_;
goto _start;
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_fst_1303_; 
v___x_1299_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1300_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
v___x_1301_ = lean_nat_sub(v_w_1135_, v___x_1300_);
lean_inc(v_tail_1145_);
lean_inc(v_tail_1151_);
v___x_1302_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1150_, v_tail_1151_, v_tail_1145_, v___x_1301_, v___y_1137_);
lean_dec(v___x_1301_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fst_1303_);
if (lean_obj_tag(v_fst_1303_) == 1)
{
lean_object* v_head_1304_; lean_object* v_snd_1305_; lean_object* v_fla_1306_; uint8_t v___x_1307_; 
v_head_1304_ = lean_ctor_get(v_fst_1303_, 0);
v_snd_1305_ = lean_ctor_get(v___x_1302_, 1);
lean_inc(v_snd_1305_);
lean_dec_ref(v___x_1302_);
v_fla_1306_ = lean_ctor_get(v_head_1304_, 0);
v___x_1307_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1306_);
if (v___x_1307_ == 0)
{
lean_object* v_out_1308_; lean_object* v_tagStack_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref_known(v_fst_1303_, 2);
v_out_1308_ = lean_ctor_get(v_snd_1305_, 0);
v_tagStack_1309_ = lean_ctor_get(v_snd_1305_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_snd_1305_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_snd_1305_, 2);
lean_dec(v_unused_1328_);
v___x_1311_ = v_snd_1305_;
v_isShared_1312_ = v_isSharedCheck_1327_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_tagStack_1309_);
lean_inc(v_out_1308_);
lean_dec(v_snd_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1327_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_out_x27_1319_; lean_object* v___x_1321_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1276_);
v___x_1314_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1276_, v___x_1313_);
v___x_1315_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1314_, v_out_1308_);
v___x_1316_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1309_);
v___x_1317_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1309_, v_tagStack_1309_, v_activeTags_1157_, v___x_1316_);
v___x_1318_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1309_);
lean_dec(v_tagStack_1309_);
v_out_x27_1319_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1315_, v___x_1317_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 2, v___x_1276_);
lean_ctor_set(v___x_1311_, 1, v___x_1318_);
lean_ctor_set(v___x_1311_, 0, v_out_x27_1319_);
v___x_1321_ = v___x_1311_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_out_x27_1319_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v___x_1276_);
v___x_1321_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v_fst_1323_; lean_object* v_snd_1324_; 
v___x_1322_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1150_, v_tail_1151_, v_tail_1145_, v_w_1135_, v___x_1321_);
v_fst_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_fst_1323_);
v_snd_1324_ = lean_ctor_get(v___x_1322_, 1);
lean_inc(v_snd_1324_);
lean_dec_ref(v___x_1322_);
v_x_1136_ = v_fst_1323_;
v___y_1137_ = v_snd_1324_;
goto _start;
}
}
}
else
{
lean_object* v_out_1329_; lean_object* v_tagStack_1330_; lean_object* v_column_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v___x_1276_);
lean_dec(v_tail_1151_);
lean_dec(v_tail_1145_);
v_out_1329_ = lean_ctor_get(v_snd_1305_, 0);
v_tagStack_1330_ = lean_ctor_get(v_snd_1305_, 1);
v_column_1331_ = lean_ctor_get(v_snd_1305_, 2);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_snd_1305_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1333_ = v_snd_1305_;
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_column_1331_);
lean_inc(v_tagStack_1330_);
lean_inc(v_out_1329_);
lean_dec(v_snd_1305_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_out_x27_1341_; lean_object* v___x_1343_; 
v___x_1335_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1299_, v_out_1329_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_column_1331_, v___x_1336_);
lean_dec(v_column_1331_);
v___x_1338_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1330_);
v___x_1339_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1330_, v_tagStack_1330_, v_activeTags_1157_, v___x_1338_);
v___x_1340_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1330_);
lean_dec(v_tagStack_1330_);
v_out_x27_1341_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1335_, v___x_1339_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 2, v___x_1337_);
lean_ctor_set(v___x_1333_, 1, v___x_1340_);
lean_ctor_set(v___x_1333_, 0, v_out_x27_1341_);
v___x_1343_ = v___x_1333_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_out_x27_1341_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v___x_1337_);
v___x_1343_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
v_x_1136_ = v_fst_1303_;
v___y_1137_ = v___x_1343_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_fst_1303_);
lean_dec(v___x_1276_);
lean_dec(v_activeTags_1157_);
lean_dec(v_tail_1151_);
lean_dec(v_tail_1145_);
v_snd_1347_ = lean_ctor_get(v___x_1302_, 1);
lean_inc(v_snd_1347_);
lean_dec_ref(v___x_1302_);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2));
v___x_1349_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_1348_, v_snd_1347_);
return v___x_1349_;
}
}
}
}
case 2:
{
uint8_t v_force_1350_; uint8_t v___x_1351_; 
lean_del_object(v___x_1159_);
lean_del_object(v___x_1153_);
lean_del_object(v___x_1147_);
v_force_1350_ = lean_ctor_get_uint8(v_f_1155_, 0);
lean_dec_ref_known(v_f_1155_, 0);
v___x_1351_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1149_);
if (v___x_1351_ == 0)
{
v___y_1202_ = v___x_1351_;
goto v___jp_1201_;
}
else
{
if (v_force_1350_ == 0)
{
v___y_1202_ = v___x_1351_;
goto v___jp_1201_;
}
else
{
goto v___jp_1161_;
}
}
}
case 3:
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1415_; 
lean_del_object(v___x_1147_);
v_a_1352_ = lean_ctor_get(v_f_1155_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_f_1155_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1354_ = v_f_1155_;
v_isShared_1355_ = v_isSharedCheck_1415_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v_f_1155_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1415_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint32_t v___x_1356_; lean_object* v_p_1357_; lean_object* v___x_1358_; uint8_t v_decide_1359_; 
v___x_1356_ = 10;
lean_inc_ref(v_a_1352_);
v_p_1357_ = lean_string_posof(v_a_1352_, v___x_1356_);
v___x_1358_ = lean_string_utf8_byte_size(v_a_1352_);
v_decide_1359_ = lean_nat_dec_eq(v_p_1357_, v___x_1358_);
if (v_decide_1359_ == 0)
{
lean_object* v_out_1360_; lean_object* v_tagStack_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1394_; 
v_out_1360_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1361_ = lean_ctor_get(v___y_1137_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___y_1137_, 2);
lean_dec(v_unused_1395_);
v___x_1363_ = v___y_1137_;
v_isShared_1364_ = v_isSharedCheck_1394_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_tagStack_1361_);
lean_inc(v_out_1360_);
lean_dec(v___y_1137_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1394_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_string_utf8_extract(v_a_1352_, v___x_1365_, v_p_1357_);
v___x_1367_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1366_, v_out_1360_);
v___x_1368_ = l_Int_toNat(v_indent_1156_);
v___x_1369_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1368_);
v___x_1370_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1368_, v___x_1369_);
v___x_1371_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1370_, v___x_1367_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 2, v___x_1368_);
lean_ctor_set(v___x_1363_, 0, v___x_1371_);
v___x_1373_ = v___x_1363_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_tagStack_1361_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v___x_1368_);
v___x_1373_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1374_ = lean_string_utf8_next(v_a_1352_, v_p_1357_);
lean_dec(v_p_1357_);
v___x_1375_ = lean_string_utf8_extract(v_a_1352_, v___x_1374_, v___x_1358_);
lean_dec(v___x_1374_);
lean_dec_ref(v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1375_);
v___x_1377_ = v___x_1354_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1377_);
v___x_1379_ = v___x_1159_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_indent_1156_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_activeTags_1157_);
v___x_1379_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v_is_1381_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1379_);
v_is_1381_ = v___x_1153_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_tail_1151_);
v_is_1381_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_box(1);
v___x_1383_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1149_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v_fst_1385_; lean_object* v_snd_1386_; 
lean_dec(v_fla_1149_);
v___x_1384_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1150_, v_is_1381_, v_tail_1145_, v_w_1135_, v___x_1373_);
v_fst_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_fst_1385_);
v_snd_1386_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_snd_1386_);
lean_dec_ref(v___x_1384_);
v_x_1136_ = v_fst_1385_;
v___y_1137_ = v_snd_1386_;
goto _start;
}
else
{
lean_object* v___x_1388_; 
v___x_1388_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_is_1381_);
v_x_1136_ = v___x_1388_;
v___y_1137_ = v___x_1373_;
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
lean_object* v_out_1396_; lean_object* v_tagStack_1397_; lean_object* v_column_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_p_1357_);
lean_del_object(v___x_1354_);
lean_del_object(v___x_1159_);
lean_dec(v_indent_1156_);
lean_del_object(v___x_1153_);
v_out_1396_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1397_ = lean_ctor_get(v___y_1137_, 1);
v_column_1398_ = lean_ctor_get(v___y_1137_, 2);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1400_ = v___y_1137_;
v_isShared_1401_ = v_isSharedCheck_1414_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_column_1398_);
lean_inc(v_tagStack_1397_);
lean_inc(v_out_1396_);
lean_dec(v___y_1137_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1414_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v_out_x27_1408_; lean_object* v___x_1410_; 
lean_inc_ref(v_a_1352_);
v___x_1402_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_1352_, v_out_1396_);
v___x_1403_ = lean_string_length(v_a_1352_);
lean_dec_ref(v_a_1352_);
v___x_1404_ = lean_nat_add(v_column_1398_, v___x_1403_);
lean_dec(v_column_1398_);
v___x_1405_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1397_);
v___x_1406_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1397_, v_tagStack_1397_, v_activeTags_1157_, v___x_1405_);
v___x_1407_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1397_);
lean_dec(v_tagStack_1397_);
v_out_x27_1408_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1402_, v___x_1406_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v___x_1404_);
lean_ctor_set(v___x_1400_, 1, v___x_1407_);
lean_ctor_set(v___x_1400_, 0, v_out_x27_1408_);
v___x_1410_ = v___x_1400_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_out_x27_1408_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v___x_1404_);
v___x_1410_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; 
v___x_1411_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1411_;
v___y_1137_ = v___x_1410_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1416_; lean_object* v_f_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_del_object(v___x_1147_);
v_indent_1416_ = lean_ctor_get(v_f_1155_, 0);
lean_inc(v_indent_1416_);
v_f_1417_ = lean_ctor_get(v_f_1155_, 1);
lean_inc(v_f_1417_);
lean_dec_ref_known(v_f_1155_, 2);
v___x_1418_ = lean_int_add(v_indent_1156_, v_indent_1416_);
lean_dec(v_indent_1416_);
lean_dec(v_indent_1156_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1418_);
lean_ctor_set(v___x_1159_, 0, v_f_1417_);
v___x_1420_ = v___x_1159_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_f_1417_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_activeTags_1157_);
v___x_1420_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1420_);
v___x_1422_ = v___x_1153_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_tail_1151_);
v___x_1422_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v___x_1422_);
v_x_1136_ = v___x_1423_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v_a_1427_ = lean_ctor_get(v_f_1155_, 0);
lean_inc(v_a_1427_);
v_a_1428_ = lean_ctor_get(v_f_1155_, 1);
lean_inc(v_a_1428_);
lean_dec_ref_known(v_f_1155_, 2);
v___x_1429_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1156_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 2, v___x_1429_);
lean_ctor_set(v___x_1159_, 0, v_a_1427_);
v___x_1431_ = v___x_1159_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_indent_1156_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1428_);
lean_ctor_set(v___x_1432_, 1, v_indent_1156_);
lean_ctor_set(v___x_1432_, 2, v_activeTags_1157_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1432_);
v___x_1434_ = v___x_1153_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_tail_1151_);
v___x_1434_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1434_);
lean_ctor_set(v___x_1147_, 0, v___x_1431_);
v___x_1436_ = v___x_1147_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v___x_1436_);
v_x_1136_ = v___x_1437_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1442_; uint8_t v_behavior_1443_; uint8_t v___x_1444_; 
lean_del_object(v___x_1147_);
v_a_1442_ = lean_ctor_get(v_f_1155_, 0);
lean_inc(v_a_1442_);
v_behavior_1443_ = lean_ctor_get_uint8(v_f_1155_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1155_, 1);
v___x_1444_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1149_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1446_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_a_1442_);
v___x_1446_ = v___x_1159_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1442_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_indent_1156_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_activeTags_1157_);
v___x_1446_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___x_1447_);
lean_ctor_set(v___x_1153_, 0, v___x_1446_);
v___x_1449_ = v___x_1153_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_fst_1452_; lean_object* v_snd_1453_; 
v___x_1450_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v___x_1451_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_1443_, v___x_1449_, v___x_1450_, v_w_1135_, v___y_1137_);
v_fst_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_fst_1452_);
v_snd_1453_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_snd_1453_);
lean_dec_ref(v___x_1451_);
v_x_1136_ = v_fst_1452_;
v___y_1137_ = v_snd_1453_;
goto _start;
}
}
}
else
{
lean_object* v___x_1458_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_a_1442_);
v___x_1458_ = v___x_1159_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1442_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_indent_1156_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_activeTags_1157_);
v___x_1458_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1458_);
v___x_1460_ = v___x_1153_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_tail_1151_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v___x_1460_);
v_x_1136_ = v___x_1461_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1465_; lean_object* v_a_1466_; lean_object* v_out_1467_; lean_object* v_tagStack_1468_; lean_object* v_column_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1492_; 
v_a_1465_ = lean_ctor_get(v_f_1155_, 0);
lean_inc(v_a_1465_);
v_a_1466_ = lean_ctor_get(v_f_1155_, 1);
lean_inc(v_a_1466_);
lean_dec_ref_known(v_f_1155_, 2);
v_out_1467_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1468_ = lean_ctor_get(v___y_1137_, 1);
v_column_1469_ = lean_ctor_get(v___y_1137_, 2);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1471_ = v___y_1137_;
v_isShared_1472_ = v_isSharedCheck_1492_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_column_1469_);
lean_inc(v_tagStack_1468_);
lean_inc(v_out_1467_);
lean_dec(v___y_1137_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1492_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1473_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_1469_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_column_1469_);
lean_ctor_set(v___x_1474_, 1, v_out_1467_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_a_1465_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_tagStack_1468_);
lean_ctor_set(v___x_1153_, 0, v___x_1475_);
v___x_1477_ = v___x_1153_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_tagStack_1468_);
v___x_1477_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1477_);
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1479_ = v___x_1471_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_column_1469_);
v___x_1479_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_add(v_activeTags_1157_, v___x_1480_);
lean_dec(v_activeTags_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 2, v___x_1481_);
lean_ctor_set(v___x_1159_, 0, v_a_1466_);
v___x_1483_ = v___x_1159_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1466_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_indent_1156_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_tail_1151_);
lean_ctor_set(v___x_1147_, 0, v___x_1483_);
v___x_1485_ = v___x_1147_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_tail_1151_);
v___x_1485_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v___x_1485_);
v_x_1136_ = v___x_1486_;
v___y_1137_ = v___x_1479_;
goto _start;
}
}
}
}
}
}
}
v___jp_1161_:
{
lean_object* v_out_1162_; lean_object* v_tagStack_1163_; lean_object* v_column_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1200_; 
v_out_1162_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1163_ = lean_ctor_get(v___y_1137_, 1);
v_column_1164_ = lean_ctor_get(v___y_1137_, 2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1166_ = v___y_1137_;
v_isShared_1167_ = v_isSharedCheck_1200_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_column_1164_);
lean_inc(v_tagStack_1163_);
lean_inc(v_out_1162_);
lean_dec(v___y_1137_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1200_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
lean_inc(v_column_1164_);
v___x_1168_ = lean_nat_to_int(v_column_1164_);
v___x_1169_ = lean_int_dec_lt(v___x_1168_, v_indent_1156_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_out_x27_1177_; lean_object* v___x_1179_; 
lean_dec(v___x_1168_);
lean_dec(v_column_1164_);
v___x_1170_ = l_Int_toNat(v_indent_1156_);
lean_dec(v_indent_1156_);
v___x_1171_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1170_);
v___x_1172_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1170_, v___x_1171_);
v___x_1173_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1172_, v_out_1162_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1163_);
v___x_1175_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1163_, v_tagStack_1163_, v_activeTags_1157_, v___x_1174_);
v___x_1176_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1163_);
lean_dec(v_tagStack_1163_);
v_out_x27_1177_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1173_, v___x_1175_);
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
v___x_1180_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1180_;
v___y_1137_ = v___x_1179_;
goto _start;
}
}
else
{
lean_object* v___x_1183_; uint32_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_out_x27_1194_; lean_object* v___x_1196_; 
v___x_1183_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_1184_ = 32;
v___x_1185_ = lean_int_sub(v_indent_1156_, v___x_1168_);
lean_dec(v___x_1168_);
lean_dec(v_indent_1156_);
v___x_1186_ = l_Int_toNat(v___x_1185_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_string_pushn(v___x_1183_, v___x_1184_, v___x_1186_);
lean_inc_ref(v___x_1187_);
v___x_1188_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1187_, v_out_1162_);
v___x_1189_ = lean_string_length(v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1190_ = lean_nat_add(v_column_1164_, v___x_1189_);
lean_dec(v_column_1164_);
v___x_1191_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1163_);
v___x_1192_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1163_, v_tagStack_1163_, v_activeTags_1157_, v___x_1191_);
v___x_1193_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1163_);
lean_dec(v_tagStack_1163_);
v_out_x27_1194_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1188_, v___x_1192_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 2, v___x_1190_);
lean_ctor_set(v___x_1166_, 1, v___x_1193_);
lean_ctor_set(v___x_1166_, 0, v_out_x27_1194_);
v___x_1196_ = v___x_1166_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_out_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v___x_1190_);
v___x_1196_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1197_;
v___y_1137_ = v___x_1196_;
goto _start;
}
}
}
}
v___jp_1201_:
{
if (v___y_1202_ == 0)
{
goto v___jp_1161_;
}
else
{
lean_object* v_out_1203_; lean_object* v_tagStack_1204_; lean_object* v_column_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_indent_1156_);
v_out_1203_ = lean_ctor_get(v___y_1137_, 0);
v_tagStack_1204_ = lean_ctor_get(v___y_1137_, 1);
v_column_1205_ = lean_ctor_get(v___y_1137_, 2);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1207_ = v___y_1137_;
v_isShared_1208_ = v_isSharedCheck_1218_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_column_1205_);
lean_inc(v_tagStack_1204_);
lean_inc(v_out_1203_);
lean_dec(v___y_1137_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1218_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_out_x27_1212_; lean_object* v___x_1214_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1157_);
lean_inc(v_tagStack_1204_);
v___x_1210_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1204_, v_tagStack_1204_, v_activeTags_1157_, v___x_1209_);
v___x_1211_ = l_List_drop___redArg(v_activeTags_1157_, v_tagStack_1204_);
lean_dec(v_tagStack_1204_);
v_out_x27_1212_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1203_, v___x_1210_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1211_);
lean_ctor_set(v___x_1207_, 0, v_out_x27_1212_);
v___x_1214_ = v___x_1207_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_out_x27_1212_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_column_1205_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1149_, v_flb_1150_, v_tail_1145_, v_tail_1151_);
v_x_1136_ = v___x_1215_;
v___y_1137_ = v___x_1214_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object* v_w_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1498_, v_x_1499_, v___y_1500_);
lean_dec(v_w_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object* v_f_1502_, lean_object* v_w_1503_, lean_object* v_indent_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1506_ = lean_box(1);
v___x_1507_ = 0;
v___x_1508_ = lean_nat_to_int(v_indent_1504_);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1510_, 0, v_f_1502_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1513_, 0, v___x_1506_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*2, v___x_1507_);
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1511_);
v___x_1515_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1503_, v___x_1514_, v___y_1505_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object* v_f_1516_, lean_object* v_w_1517_, lean_object* v_indent_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1516_, v_w_1517_, v_indent_1518_, v___y_1519_);
lean_dec(v_w_1517_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object* v_f_1521_, lean_object* v_indent_1522_, lean_object* v_w_1523_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v_snd_1526_; lean_object* v_out_1527_; 
v___x_1524_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1));
v___x_1525_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1521_, v_w_1523_, v_indent_1522_, v___x_1524_);
v_snd_1526_ = lean_ctor_get(v___x_1525_, 1);
lean_inc(v_snd_1526_);
lean_dec_ref(v___x_1525_);
v_out_1527_ = lean_ctor_get(v_snd_1526_, 0);
lean_inc_ref(v_out_1527_);
lean_dec(v_snd_1526_);
return v_out_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object* v_f_1528_, lean_object* v_indent_1529_, lean_object* v_w_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_1528_, v_indent_1529_, v_w_1530_);
lean_dec(v_w_1530_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_nat_to_int(v_a_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object* v_acc_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_array_get_size(v_a_1535_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_nat_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_sub(v___x_1536_, v___x_1540_);
v___x_1542_ = lean_array_get_borrowed(v___x_1539_, v_a_1535_, v___x_1541_);
switch(lean_obj_tag(v___x_1542_))
{
case 0:
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v___x_1541_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v___x_1544_ = lean_string_append(v_acc_1534_, v_a_1543_);
v___x_1545_ = lean_array_pop(v_a_1535_);
v_acc_1534_ = v___x_1544_;
v_a_1535_ = v___x_1545_;
goto _start;
}
case 1:
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v___x_1541_);
v_a_1547_ = lean_ctor_get(v___x_1542_, 0);
lean_inc_ref(v_a_1547_);
v___x_1548_ = lean_array_pop(v_a_1535_);
v___x_1549_ = l_Array_reverse___redArg(v_a_1547_);
v___x_1550_ = l_Array_append___redArg(v___x_1548_, v___x_1549_);
lean_dec_ref(v___x_1549_);
v_a_1535_ = v___x_1550_;
goto _start;
}
default: 
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1542_, 1);
lean_inc_ref(v_a_1552_);
v___x_1553_ = lean_array_set(v_a_1535_, v___x_1541_, v_a_1552_);
lean_dec(v___x_1541_);
v_a_1535_ = v___x_1553_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_1535_);
return v_acc_1534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object* v_00_u03b1_1555_, lean_object* v_acc_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v_acc_1556_, v_a_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object* v_tt_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1560_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_mk_empty_array_with_capacity(v___x_1561_);
v___x_1563_ = lean_array_push(v___x_1562_, v_tt_1559_);
v___x_1564_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v___x_1560_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object* v_00_u03b1_1565_, lean_object* v_tt_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1566_);
return v___x_1567_;
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

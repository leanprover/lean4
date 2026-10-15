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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Widget_TaggedText_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Widget_TaggedText_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 2)
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_14_);
lean_dec_ref_known(v_t_11_, 2);
v___x_15_ = lean_apply_2(v_k_12_, v_a_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_16_);
lean_dec_ref(v_t_11_);
v___x_17_ = lean_apply_1(v_k_12_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim(lean_object* v_00_u03b1_18_, lean_object* v_motive__1_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_ctorElim___boxed(lean_object* v_00_u03b1_25_, lean_object* v_motive__1_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Widget_TaggedText_ctorElim(v_00_u03b1_25_, v_motive__1_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_text_elim___redArg(lean_object* v_t_32_, lean_object* v_text_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_32_, v_text_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_text_elim(lean_object* v_00_u03b1_35_, lean_object* v_motive__1_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_text_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_37_, v_text_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_append_elim___redArg(lean_object* v_t_41_, lean_object* v_append_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_41_, v_append_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_append_elim(lean_object* v_00_u03b1_44_, lean_object* v_motive__1_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_append_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_46_, v_append_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_tag_elim___redArg(lean_object* v_t_50_, lean_object* v_tag_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_50_, v_tag_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_tag_elim(lean_object* v_00_u03b1_53_, lean_object* v_motive__1_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_tag_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_55_, v_tag_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__1));
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg___boxed(lean_object* v___dummy_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v_res_65_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object* v_00_u03b1_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg(){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg___boxed(lean_object* v___dummy_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Widget_instInhabitedTaggedText___redArg();
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText(lean_object* v_a_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed(lean_object* v_inst_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_75_, v_x_76_, v_x_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq___redArg(lean_object* v_inst_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
switch(lean_obj_tag(v_x_81_))
{
case 0:
{
lean_dec_ref(v_inst_80_);
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v_a_84_; uint8_t v___x_85_; 
v_a_83_ = lean_ctor_get(v_x_81_, 0);
lean_inc_ref(v_a_83_);
lean_dec_ref_known(v_x_81_, 1);
v_a_84_ = lean_ctor_get(v_x_82_, 0);
lean_inc_ref(v_a_84_);
lean_dec_ref_known(v_x_82_, 1);
v___x_85_ = lean_string_dec_eq(v_a_83_, v_a_84_);
lean_dec_ref(v_a_84_);
lean_dec_ref(v_a_83_);
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
lean_dec_ref_known(v_x_81_, 1);
lean_dec_ref(v_x_82_);
v___x_86_ = 0;
return v___x_86_;
}
}
case 1:
{
if (lean_obj_tag(v_x_82_) == 1)
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_a_87_ = lean_ctor_get(v_x_81_, 0);
lean_inc_ref(v_a_87_);
lean_dec_ref_known(v_x_81_, 1);
v_a_88_ = lean_ctor_get(v_x_82_, 0);
lean_inc_ref(v_a_88_);
lean_dec_ref_known(v_x_82_, 1);
v___x_89_ = lean_array_get_size(v_a_87_);
v___x_90_ = lean_array_get_size(v_a_88_);
v___x_91_ = lean_nat_dec_eq(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec_ref(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec_ref(v_inst_80_);
return v___x_91_;
}
else
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_92_, 0, v_inst_80_);
v___x_93_ = l_Array_isEqvAux___redArg(v_a_87_, v_a_88_, v___x_92_, v___x_89_);
lean_dec_ref(v_a_88_);
lean_dec_ref(v_a_87_);
return v___x_93_;
}
}
else
{
uint8_t v___x_94_; 
lean_dec_ref_known(v_x_81_, 1);
lean_dec_ref(v_x_82_);
lean_dec_ref(v_inst_80_);
v___x_94_ = 0;
return v___x_94_;
}
}
default: 
{
if (lean_obj_tag(v_x_82_) == 2)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_a_95_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_a_95_);
v_a_96_ = lean_ctor_get(v_x_81_, 1);
lean_inc_ref(v_a_96_);
lean_dec_ref_known(v_x_81_, 2);
v_a_97_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v_x_82_, 1);
lean_inc_ref(v_a_98_);
lean_dec_ref_known(v_x_82_, 2);
lean_inc_ref(v_inst_80_);
v___x_99_ = lean_apply_2(v_inst_80_, v_a_95_, v_a_97_);
v___x_100_ = lean_unbox(v___x_99_);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
lean_dec_ref(v_a_98_);
lean_dec_ref(v_a_96_);
lean_dec_ref(v_inst_80_);
v___x_101_ = lean_unbox(v___x_99_);
return v___x_101_;
}
else
{
v_x_81_ = v_a_96_;
v_x_82_ = v_a_98_;
goto _start;
}
}
else
{
uint8_t v___x_103_; 
lean_dec_ref_known(v_x_81_, 2);
lean_dec_ref(v_x_82_);
lean_dec_ref(v_inst_80_);
v___x_103_ = 0;
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instBEqTaggedText_beq(lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_105_, v_x_106_, v_x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___boxed(lean_object* v_00_u03b1_109_, lean_object* v_inst_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Lean_Widget_instBEqTaggedText_beq(v_00_u03b1_109_, v_inst_110_, v_x_111_, v_x_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText___redArg(lean_object* v_inst_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, v_inst_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText(lean_object* v_00_u03b1_117_, lean_object* v_inst_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_119_, 0, lean_box(0));
lean_closure_set(v___x_119_, 1, v_inst_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(2u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(lean_object* v_inst_142_, lean_object* v_x_143_, lean_object* v_prec_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_142_, v_x_143_, v_prec_144_);
lean_dec(v_prec_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg(lean_object* v_inst_146_, lean_object* v_x_147_, lean_object* v_prec_148_){
_start:
{
switch(lean_obj_tag(v_x_147_))
{
case 0:
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v_inst_146_);
v_a_149_ = lean_ctor_get(v_x_147_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_169_ == 0)
{
v___x_151_ = v_x_147_;
v_isShared_152_ = v_isSharedCheck_169_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v_x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_169_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___y_154_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1024u);
v___x_166_ = lean_nat_dec_le(v___x_165_, v_prec_148_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_154_ = v___x_167_;
goto v___jp_153_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_154_ = v___x_168_;
goto v___jp_153_;
}
v___jp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2));
v___x_156_ = l_String_quote(v_a_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 3);
lean_ctor_set(v___x_151_, 0, v___x_156_);
v___x_158_ = v___x_151_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_164_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_155_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
lean_inc(v___y_154_);
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___y_154_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = 0;
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_161_);
v___x_163_ = l_Repr_addAppParen(v___x_162_, v_prec_148_);
return v___x_163_;
}
}
}
}
case 1:
{
lean_object* v_a_170_; lean_object* v_localinst_171_; lean_object* v___y_173_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_a_170_ = lean_ctor_get(v_x_147_, 0);
lean_inc_ref(v_a_170_);
lean_dec_ref_known(v_x_147_, 1);
v_localinst_171_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_171_, 0, v_inst_146_);
v___x_181_ = lean_unsigned_to_nat(1024u);
v___x_182_ = lean_nat_dec_le(v___x_181_, v_prec_148_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_173_ = v___x_183_;
goto v___jp_172_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_173_ = v___x_184_;
goto v___jp_172_;
}
v___jp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_174_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7));
v___x_175_ = l_Array_repr___redArg(v_localinst_171_, v_a_170_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_inc(v___y_173_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___y_173_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_178_);
v___x_180_ = l_Repr_addAppParen(v___x_179_, v_prec_148_);
return v___x_180_;
}
}
default: 
{
lean_object* v_a_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_209_; 
v_a_185_ = lean_ctor_get(v_x_147_, 0);
v_a_186_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_209_ == 0)
{
v___x_188_ = v_x_147_;
v_isShared_189_ = v_isSharedCheck_209_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_inc(v_a_185_);
lean_dec(v_x_147_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_209_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___y_192_; uint8_t v___x_206_; 
v___x_190_ = lean_unsigned_to_nat(1024u);
v___x_206_ = lean_nat_dec_le(v___x_190_, v_prec_148_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_192_ = v___x_207_;
goto v___jp_191_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_192_ = v___x_208_;
goto v___jp_191_;
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_193_ = lean_box(1);
v___x_194_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10));
lean_inc_ref(v_inst_146_);
v___x_195_ = lean_apply_2(v_inst_146_, v_a_185_, v___x_190_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 5);
lean_ctor_set(v___x_188_, 1, v___x_195_);
lean_ctor_set(v___x_188_, 0, v___x_194_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_205_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_193_);
v___x_199_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_146_, v_a_186_, v___x_190_);
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_inc(v___y_192_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___y_192_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
v___x_204_ = l_Repr_addAppParen(v___x_203_, v_prec_148_);
return v___x_204_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr(lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_x_212_, lean_object* v_prec_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_211_, v_x_212_, v_prec_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___boxed(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Widget_instReprTaggedText_repr(v_00_u03b1_215_, v_inst_216_, v_x_217_, v_prec_218_);
lean_dec(v_prec_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText___redArg(lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, v_inst_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, v_inst_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(lean_object* v_inst_234_, lean_object* v_json_235_){
_start:
{
lean_object* v___x_236_; 
lean_inc(v_json_235_);
v___x_236_ = l_Lean_Json_getTag_x3f(v_json_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
lean_dec(v_json_235_);
lean_dec_ref(v_inst_234_);
v___x_237_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1));
return v___x_237_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_355_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_355_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_355_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_355_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_244_ = lean_string_dec_eq(v_val_238_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
v___x_246_ = lean_string_dec_eq(v_val_238_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; uint8_t v___x_248_; 
lean_del_object(v___x_240_);
v___x_247_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
v___x_248_ = lean_string_dec_eq(v_val_238_, v___x_247_);
lean_dec(v_val_238_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_dec(v_json_235_);
lean_dec_ref(v_inst_234_);
v___x_249_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6));
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(2u);
v___x_251_ = lean_box(0);
v___x_252_ = l_Lean_Json_parseCtorFields(v_json_235_, v___x_247_, v___x_250_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_inst_234_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_252_, 1);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_array_get_borrowed(v___x_242_, v_a_261_, v___x_262_);
lean_inc_ref(v_inst_234_);
lean_inc(v___x_263_);
v___x_264_ = lean_apply_1(v_inst_234_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_a_261_);
lean_dec_ref(v_inst_234_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_273_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_264_, 1);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_array_get(v___x_242_, v_a_261_, v___x_274_);
lean_dec(v_a_261_);
v___x_276_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_234_, v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_dec(v_a_273_);
return v___x_276_;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_285_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_273_);
lean_ctor_set(v___x_281_, 1, v_a_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_val_238_);
lean_dec_ref(v_inst_234_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_box(0);
v___x_288_ = l_Lean_Json_parseCtorFields(v_json_235_, v___x_245_, v___x_286_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_del_object(v___x_240_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_a_297_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_288_, 1);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_array_get(v___x_242_, v_a_297_, v___x_298_);
lean_dec(v_a_297_);
v___x_300_ = l_Lean_Json_getStr_x3f(v___x_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_del_object(v___x_240_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_319_; 
v_a_309_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_319_ == 0)
{
v___x_311_ = v___x_300_;
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_300_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 0);
lean_ctor_set(v___x_240_, 0, v_a_309_);
v___x_314_ = v___x_240_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_val_238_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_box(0);
v___x_322_ = l_Lean_Json_parseCtorFields(v_json_235_, v___x_243_, v___x_320_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_del_object(v___x_240_);
lean_dec_ref(v_inst_234_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v_localinst_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_a_331_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_322_, 1);
v_localinst_332_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg), 2, 1);
lean_closure_set(v_localinst_332_, 0, v_inst_234_);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_array_get(v___x_242_, v_a_331_, v___x_333_);
lean_dec(v_a_331_);
v___x_335_ = l_Lean_Array_fromJson_x3f___redArg(v_localinst_332_, v___x_334_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_del_object(v___x_240_);
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_354_; 
v_a_344_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_354_ == 0)
{
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v_a_344_);
v___x_349_ = v___x_240_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_json_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_357_, v_json_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText___redArg(lean_object* v_inst_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_361_, 0, lean_box(0));
lean_closure_set(v___x_361_, 1, v_inst_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_364_, 0, lean_box(0));
lean_closure_set(v___x_364_, 1, v_inst_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___redArg(lean_object* v_inst_365_, lean_object* v_x_366_){
_start:
{
switch(lean_obj_tag(v_x_366_))
{
case 0:
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_inst_365_);
v_a_367_ = lean_ctor_get(v_x_366_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_379_ == 0)
{
v___x_369_ = v_x_366_;
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v_x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 3);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_367_);
v___x_373_ = v_reuseFailAlloc_378_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_371_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_Json_mkObj(v___x_376_);
lean_dec_ref_known(v___x_376_, 2);
return v___x_377_;
}
}
}
case 1:
{
lean_object* v_a_380_; lean_object* v_localinst_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_380_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_a_380_);
lean_dec_ref_known(v_x_366_, 1);
v_localinst_381_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson___redArg), 2, 1);
lean_closure_set(v_localinst_381_, 0, v_inst_365_);
v___x_382_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_383_ = l_Lean_Array_toJson___redArg(v_localinst_381_, v_a_380_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_Json_mkObj(v___x_386_);
lean_dec_ref_known(v___x_386_, 2);
return v___x_387_;
}
default: 
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_407_; 
v_a_388_ = lean_ctor_get(v_x_366_, 0);
v_a_389_ = lean_ctor_get(v_x_366_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_407_ == 0)
{
v___x_391_ = v_x_366_;
v_isShared_392_ = v_isSharedCheck_407_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_inc(v_a_388_);
lean_dec(v_x_366_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_407_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_393_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
lean_inc_ref(v_inst_365_);
v___x_394_ = lean_apply_1(v_inst_365_, v_a_388_);
v___x_395_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_365_, v_a_389_);
v___x_396_ = lean_unsigned_to_nat(2u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_396_);
v___x_398_ = lean_array_push(v___x_397_, v___x_394_);
v___x_399_ = lean_array_push(v___x_398_, v___x_395_);
v___x_400_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 0);
lean_ctor_set(v___x_391_, 1, v___x_400_);
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_402_ = v___x_391_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_400_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = l_Lean_Json_mkObj(v___x_404_);
lean_dec_ref_known(v___x_404_, 2);
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson(lean_object* v_00_u03b1_408_, lean_object* v_inst_409_, lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_409_, v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText___redArg(lean_object* v_inst_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_413_, 0, lean_box(0));
lean_closure_set(v___x_413_, 1, v_inst_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText(lean_object* v_00_u03b1_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_416_, 0, lean_box(0));
lean_closure_set(v___x_416_, 1, v_inst_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText___redArg(lean_object* v_s_u2080_417_, lean_object* v_x_418_){
_start:
{
switch(lean_obj_tag(v_x_418_))
{
case 0:
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_a_419_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v_x_418_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v_x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_string_append(v_a_419_, v_s_u2080_417_);
lean_dec_ref(v_s_u2080_417_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
case 1:
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_455_; 
v_a_428_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_455_ == 0)
{
v___x_430_ = v_x_418_;
v_isShared_431_ = v_isSharedCheck_455_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v_x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_455_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_432_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
v___x_433_ = lean_array_get_size(v_a_428_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_sub(v___x_433_, v___x_434_);
v___x_436_ = lean_array_get(v___x_432_, v_a_428_, v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_449_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_449_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_449_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_449_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_string_append(v_a_437_, v_s_u2080_417_);
lean_dec_ref(v_s_u2080_417_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_448_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_array_set(v_a_428_, v___x_435_, v___x_443_);
lean_dec(v___x_435_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_444_);
v___x_446_ = v___x_430_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v___x_451_; 
lean_dec(v___x_436_);
lean_dec(v___x_435_);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
lean_ctor_set(v___x_430_, 0, v_s_u2080_417_);
v___x_451_ = v___x_430_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_s_u2080_417_);
v___x_451_ = v_reuseFailAlloc_454_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_array_push(v_a_428_, v___x_451_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
}
default: 
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v_s_u2080_417_);
v___x_457_ = lean_unsigned_to_nat(2u);
v___x_458_ = lean_mk_empty_array_with_capacity(v___x_457_);
v___x_459_ = lean_array_push(v___x_458_, v_x_418_);
v___x_460_ = lean_array_push(v___x_459_, v___x_456_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText(lean_object* v_00_u03b1_462_, lean_object* v_s_u2080_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_u2080_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag___redArg(lean_object* v_acc_466_, lean_object* v_t_u2080_467_, lean_object* v_a_u2080_468_){
_start:
{
lean_object* v_a_470_; 
switch(lean_obj_tag(v_acc_466_))
{
case 1:
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
v_a_477_ = lean_ctor_get(v_acc_466_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_acc_466_);
if (v_isSharedCheck_486_ == 0)
{
v___x_479_ = v_acc_466_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v_acc_466_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_481_, 0, v_t_u2080_467_);
lean_ctor_set(v___x_481_, 1, v_a_u2080_468_);
v___x_482_ = lean_array_push(v_a_477_, v___x_481_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
case 0:
{
lean_object* v_a_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_a_487_ = lean_ctor_get(v_acc_466_, 0);
v___x_488_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_489_ = lean_string_dec_eq(v_a_487_, v___x_488_);
if (v___x_489_ == 0)
{
v_a_470_ = v_acc_466_;
goto v___jp_469_;
}
else
{
lean_object* v___x_490_; 
lean_dec_ref_known(v_acc_466_, 1);
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v_t_u2080_467_);
lean_ctor_set(v___x_490_, 1, v_a_u2080_468_);
return v___x_490_;
}
}
default: 
{
v_a_470_ = v_acc_466_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_471_, 0, v_t_u2080_467_);
lean_ctor_set(v___x_471_, 1, v_a_u2080_468_);
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = lean_mk_empty_array_with_capacity(v___x_472_);
v___x_474_ = lean_array_push(v___x_473_, v_a_470_);
v___x_475_ = lean_array_push(v___x_474_, v___x_471_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag(lean_object* v_00_u03b1_491_, lean_object* v_acc_492_, lean_object* v_t_u2080_493_, lean_object* v_a_u2080_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_acc_492_, v_t_u2080_493_, v_a_u2080_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(lean_object* v_f_496_, size_t v_sz_497_, size_t v_i_498_, lean_object* v_bs_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_lt(v_i_498_, v_sz_497_);
if (v___x_500_ == 0)
{
lean_dec(v_f_496_);
return v_bs_499_;
}
else
{
lean_object* v_v_501_; lean_object* v___x_502_; lean_object* v_bs_x27_503_; lean_object* v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_v_501_ = lean_array_uget(v_bs_499_, v_i_498_);
v___x_502_ = lean_unsigned_to_nat(0u);
v_bs_x27_503_ = lean_array_uset(v_bs_499_, v_i_498_, v___x_502_);
lean_inc(v_f_496_);
v___x_504_ = l_Lean_Widget_TaggedText_map___redArg(v_f_496_, v_v_501_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_498_, v___x_505_);
v___x_507_ = lean_array_uset(v_bs_x27_503_, v_i_498_, v___x_504_);
v_i_498_ = v___x_506_;
v_bs_499_ = v___x_507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map___redArg(lean_object* v_f_509_, lean_object* v_x_510_){
_start:
{
switch(lean_obj_tag(v_x_510_))
{
case 0:
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_f_509_);
v_a_511_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v_x_510_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v_x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
case 1:
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v_a_519_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v_x_510_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v_x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v_sz_523_ = lean_array_size(v_a_519_);
v___x_524_ = ((size_t)0ULL);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_509_, v_sz_523_, v___x_524_, v_a_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
default: 
{
lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
v_a_530_ = lean_ctor_get(v_x_510_, 0);
v_a_531_ = lean_ctor_get(v_x_510_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_540_ == 0)
{
v___x_533_ = v_x_510_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_inc(v_a_530_);
lean_dec(v_x_510_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
lean_inc(v_f_509_);
v___x_535_ = lean_apply_1(v_f_509_, v_a_530_);
v___x_536_ = l_Lean_Widget_TaggedText_map___redArg(v_f_509_, v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_536_);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg___boxed(lean_object* v_f_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_bs_544_){
_start:
{
size_t v_sz_boxed_545_; size_t v_i_boxed_546_; lean_object* v_res_547_; 
v_sz_boxed_545_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_546_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_541_, v_sz_boxed_545_, v_i_boxed_546_, v_bs_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_f_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Widget_TaggedText_map___redArg(v_f_550_, v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_f_555_, size_t v_sz_556_, size_t v_i_557_, lean_object* v_bs_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_555_, v_sz_556_, v_i_557_, v_bs_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_f_562_, lean_object* v_sz_563_, lean_object* v_i_564_, lean_object* v_bs_565_){
_start:
{
size_t v_sz_boxed_566_; size_t v_i_boxed_567_; lean_object* v_res_568_; 
v_sz_boxed_566_ = lean_unbox_usize(v_sz_563_);
lean_dec(v_sz_563_);
v_i_boxed_567_ = lean_unbox_usize(v_i_564_);
lean_dec(v_i_564_);
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(v_00_u03b1_560_, v_00_u03b2_561_, v_f_562_, v_sz_boxed_566_, v_i_boxed_567_, v_bs_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__0(lean_object* v_toPure_569_, lean_object* v_____do__lift_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_____do__lift_570_);
v___x_572_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__1(lean_object* v_____do__lift_573_, lean_object* v_toPure_574_, lean_object* v_____do__lift_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v_____do__lift_573_);
lean_ctor_set(v___x_576_, 1, v_____do__lift_575_);
v___x_577_ = lean_apply_2(v_toPure_574_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object* v_inst_578_, lean_object* v_f_579_, lean_object* v_x_580_){
_start:
{
switch(lean_obj_tag(v_x_580_))
{
case 0:
{
lean_object* v_toApplicative_581_; lean_object* v_toPure_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v_toApplicative_581_ = lean_ctor_get(v_inst_578_, 0);
lean_inc_ref(v_toApplicative_581_);
lean_dec(v_f_579_);
lean_dec_ref(v_inst_578_);
v_toPure_582_ = lean_ctor_get(v_toApplicative_581_, 1);
lean_inc(v_toPure_582_);
lean_dec_ref(v_toApplicative_581_);
v_a_583_ = lean_ctor_get(v_x_580_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_591_ == 0)
{
v___x_585_ = v_x_580_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v_x_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_2(v_toPure_582_, lean_box(0), v___x_588_);
return v___x_589_;
}
}
}
case 1:
{
lean_object* v_toApplicative_592_; lean_object* v_toBind_593_; lean_object* v_toPure_594_; lean_object* v_a_595_; lean_object* v___f_596_; lean_object* v___x_597_; size_t v_sz_598_; size_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_toApplicative_592_ = lean_ctor_get(v_inst_578_, 0);
v_toBind_593_ = lean_ctor_get(v_inst_578_, 1);
lean_inc(v_toBind_593_);
v_toPure_594_ = lean_ctor_get(v_toApplicative_592_, 1);
v_a_595_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_a_595_);
lean_dec_ref_known(v_x_580_, 1);
lean_inc(v_toPure_594_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_596_, 0, v_toPure_594_);
lean_inc_ref(v_inst_578_);
v___x_597_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg), 3, 2);
lean_closure_set(v___x_597_, 0, v_inst_578_);
lean_closure_set(v___x_597_, 1, v_f_579_);
v_sz_598_ = lean_array_size(v_a_595_);
v___x_599_ = ((size_t)0ULL);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_578_, v___x_597_, v_sz_598_, v___x_599_, v_a_595_);
v___x_601_ = lean_apply_4(v_toBind_593_, lean_box(0), lean_box(0), v___x_600_, v___f_596_);
return v___x_601_;
}
default: 
{
lean_object* v_toApplicative_602_; lean_object* v_toBind_603_; lean_object* v_toPure_604_; lean_object* v_a_605_; lean_object* v_a_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_toApplicative_602_ = lean_ctor_get(v_inst_578_, 0);
v_toBind_603_ = lean_ctor_get(v_inst_578_, 1);
lean_inc_n(v_toBind_603_, 2);
v_toPure_604_ = lean_ctor_get(v_toApplicative_602_, 1);
lean_inc(v_toPure_604_);
v_a_605_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_a_605_);
v_a_606_ = lean_ctor_get(v_x_580_, 1);
lean_inc_ref(v_a_606_);
lean_dec_ref_known(v_x_580_, 2);
lean_inc(v_f_579_);
v___f_607_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_607_, 0, v_toPure_604_);
lean_closure_set(v___f_607_, 1, v_inst_578_);
lean_closure_set(v___f_607_, 2, v_f_579_);
lean_closure_set(v___f_607_, 3, v_a_606_);
lean_closure_set(v___f_607_, 4, v_toBind_603_);
v___x_608_ = lean_apply_1(v_f_579_, v_a_605_);
v___x_609_ = lean_apply_4(v_toBind_603_, lean_box(0), lean_box(0), v___x_608_, v___f_607_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__2(lean_object* v_toPure_610_, lean_object* v_inst_611_, lean_object* v_f_612_, lean_object* v_a_613_, lean_object* v_toBind_614_, lean_object* v_____do__lift_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___f_616_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_616_, 0, v_____do__lift_615_);
lean_closure_set(v___f_616_, 1, v_toPure_610_);
v___x_617_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_611_, v_f_612_, v_a_613_);
v___x_618_ = lean_apply_4(v_toBind_614_, lean_box(0), lean_box(0), v___x_617_, v___f_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM(lean_object* v_m_619_, lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_inst_622_, lean_object* v_f_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_622_, v_f_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__1(lean_object* v_inst_626_, lean_object* v_f_627_, lean_object* v_a_628_, lean_object* v_____r_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_626_, v_f_627_, v_a_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg(lean_object* v_inst_631_, lean_object* v_f_632_, lean_object* v_x_633_){
_start:
{
switch(lean_obj_tag(v_x_633_))
{
case 0:
{
lean_object* v_toApplicative_634_; lean_object* v_toPure_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_toApplicative_634_ = lean_ctor_get(v_inst_631_, 0);
lean_inc_ref(v_toApplicative_634_);
lean_dec_ref_known(v_x_633_, 1);
lean_dec(v_f_632_);
lean_dec_ref(v_inst_631_);
v_toPure_635_ = lean_ctor_get(v_toApplicative_634_, 1);
lean_inc(v_toPure_635_);
lean_dec_ref(v_toApplicative_634_);
v___x_636_ = lean_box(0);
v___x_637_ = lean_apply_2(v_toPure_635_, lean_box(0), v___x_636_);
return v___x_637_;
}
case 1:
{
lean_object* v_toApplicative_638_; lean_object* v_toPure_639_; lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_toApplicative_638_ = lean_ctor_get(v_inst_631_, 0);
v_toPure_639_ = lean_ctor_get(v_toApplicative_638_, 1);
v_a_640_ = lean_ctor_get(v_x_633_, 0);
lean_inc_ref(v_a_640_);
lean_dec_ref_known(v_x_633_, 1);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_array_get_size(v_a_640_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_nat_dec_lt(v___x_641_, v___x_642_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_inc(v_toPure_639_);
lean_dec_ref(v_a_640_);
lean_dec(v_f_632_);
lean_dec_ref(v_inst_631_);
v___x_645_ = lean_apply_2(v_toPure_639_, lean_box(0), v___x_643_);
return v___x_645_;
}
else
{
lean_object* v___f_646_; uint8_t v___x_647_; 
lean_inc_ref(v_inst_631_);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_646_, 0, v_inst_631_);
lean_closure_set(v___f_646_, 1, v_f_632_);
v___x_647_ = lean_nat_dec_le(v___x_642_, v___x_642_);
if (v___x_647_ == 0)
{
if (v___x_644_ == 0)
{
lean_object* v___x_648_; 
lean_inc(v_toPure_639_);
lean_dec_ref(v___f_646_);
lean_dec_ref(v_a_640_);
lean_dec_ref(v_inst_631_);
v___x_648_ = lean_apply_2(v_toPure_639_, lean_box(0), v___x_643_);
return v___x_648_;
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_642_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_631_, v___f_646_, v_a_640_, v___x_649_, v___x_650_, v___x_643_);
return v___x_651_;
}
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_642_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_631_, v___f_646_, v_a_640_, v___x_652_, v___x_653_, v___x_643_);
return v___x_654_;
}
}
}
default: 
{
lean_object* v_toBind_655_; lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_toBind_655_ = lean_ctor_get(v_inst_631_, 1);
lean_inc(v_toBind_655_);
v_a_656_ = lean_ctor_get(v_x_633_, 0);
lean_inc(v_a_656_);
v_a_657_ = lean_ctor_get(v_x_633_, 1);
lean_inc_ref_n(v_a_657_, 2);
lean_dec_ref_known(v_x_633_, 2);
lean_inc(v_f_632_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_658_, 0, v_inst_631_);
lean_closure_set(v___f_658_, 1, v_f_632_);
lean_closure_set(v___f_658_, 2, v_a_657_);
v___x_659_ = lean_apply_2(v_f_632_, v_a_656_, v_a_657_);
v___x_660_ = lean_apply_4(v_toBind_655_, lean_box(0), lean_box(0), v___x_659_, v___f_658_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__0(lean_object* v_inst_661_, lean_object* v_f_662_, lean_object* v_x_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_661_, v_f_662_, v___y_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM(lean_object* v_m_666_, lean_object* v_00_u03b1_667_, lean_object* v_inst_668_, lean_object* v_f_669_, lean_object* v_x_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_668_, v_f_669_, v_x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(lean_object* v_f_672_, size_t v_sz_673_, size_t v_i_674_, lean_object* v_bs_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_lt(v_i_674_, v_sz_673_);
if (v___x_676_ == 0)
{
lean_dec_ref(v_f_672_);
return v_bs_675_;
}
else
{
lean_object* v_v_677_; lean_object* v___x_678_; lean_object* v_bs_x27_679_; lean_object* v___x_680_; size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v_v_677_ = lean_array_uget(v_bs_675_, v_i_674_);
v___x_678_ = lean_unsigned_to_nat(0u);
v_bs_x27_679_ = lean_array_uset(v_bs_675_, v_i_674_, v___x_678_);
lean_inc_ref(v_f_672_);
v___x_680_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_672_, v_v_677_);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_674_, v___x_681_);
v___x_683_ = lean_array_uset(v_bs_x27_679_, v_i_674_, v___x_680_);
v_i_674_ = v___x_682_;
v_bs_675_ = v___x_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object* v_f_685_, lean_object* v_x_686_){
_start:
{
switch(lean_obj_tag(v_x_686_))
{
case 0:
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_f_685_);
v_a_687_ = lean_ctor_get(v_x_686_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v_x_686_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v_x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
case 1:
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
v_a_695_ = lean_ctor_get(v_x_686_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_705_ == 0)
{
v___x_697_ = v_x_686_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v_x_686_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
size_t v_sz_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v_sz_699_ = lean_array_size(v_a_695_);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_685_, v_sz_699_, v___x_700_, v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_701_);
v___x_703_ = v___x_697_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
default: 
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v_x_686_, 0);
lean_inc(v_a_706_);
v_a_707_ = lean_ctor_get(v_x_686_, 1);
lean_inc_ref(v_a_707_);
lean_dec_ref_known(v_x_686_, 2);
v___x_708_ = lean_apply_2(v_f_685_, v_a_706_, v_a_707_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg___boxed(lean_object* v_f_709_, lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_){
_start:
{
size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v_sz_boxed_713_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_709_, v_sz_boxed_713_, v_i_boxed_714_, v_bs_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_f_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_f_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_bs_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_723_, v_sz_724_, v_i_725_, v_bs_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_f_730_, lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_bs_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_735_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(v_00_u03b1_728_, v_00_u03b2_729_, v_f_730_, v_sz_boxed_734_, v_i_boxed_735_, v_bs_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___redArg(lean_object* v_inst_737_, lean_object* v_f_738_, lean_object* v_x_739_){
_start:
{
switch(lean_obj_tag(v_x_739_))
{
case 0:
{
lean_object* v_toApplicative_740_; lean_object* v_toPure_741_; lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_toApplicative_740_ = lean_ctor_get(v_inst_737_, 0);
lean_inc_ref(v_toApplicative_740_);
lean_dec(v_f_738_);
lean_dec_ref(v_inst_737_);
v_toPure_741_ = lean_ctor_get(v_toApplicative_740_, 1);
lean_inc(v_toPure_741_);
lean_dec_ref(v_toApplicative_740_);
v_a_742_ = lean_ctor_get(v_x_739_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v_x_739_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v_x_739_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_apply_2(v_toPure_741_, lean_box(0), v___x_747_);
return v___x_748_;
}
}
}
case 1:
{
lean_object* v_toApplicative_751_; lean_object* v_toBind_752_; lean_object* v_toPure_753_; lean_object* v_a_754_; lean_object* v___f_755_; lean_object* v___x_756_; size_t v_sz_757_; size_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_toApplicative_751_ = lean_ctor_get(v_inst_737_, 0);
v_toBind_752_ = lean_ctor_get(v_inst_737_, 1);
lean_inc(v_toBind_752_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_751_, 1);
v_a_754_ = lean_ctor_get(v_x_739_, 0);
lean_inc_ref(v_a_754_);
lean_dec_ref_known(v_x_739_, 1);
lean_inc(v_toPure_753_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_755_, 0, v_toPure_753_);
lean_inc_ref(v_inst_737_);
v___x_756_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_rewriteM___redArg), 3, 2);
lean_closure_set(v___x_756_, 0, v_inst_737_);
lean_closure_set(v___x_756_, 1, v_f_738_);
v_sz_757_ = lean_array_size(v_a_754_);
v___x_758_ = ((size_t)0ULL);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_737_, v___x_756_, v_sz_757_, v___x_758_, v_a_754_);
v___x_760_ = lean_apply_4(v_toBind_752_, lean_box(0), lean_box(0), v___x_759_, v___f_755_);
return v___x_760_;
}
default: 
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_763_; 
lean_dec_ref(v_inst_737_);
v_a_761_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_a_761_);
v_a_762_ = lean_ctor_get(v_x_739_, 1);
lean_inc_ref(v_a_762_);
lean_dec_ref_known(v_x_739_, 2);
v___x_763_ = lean_apply_2(v_f_738_, v_a_761_, v_a_762_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM(lean_object* v_m_764_, lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_inst_767_, lean_object* v_f_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Widget_TaggedText_rewriteM___redArg(v_inst_767_, v_f_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(lean_object* v_inst_771_, lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v_a_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_rpcEncode_776_; lean_object* v___x_648__overap_777_; lean_object* v___x_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_rpcEncode_776_ = lean_ctor_get(v_inst_771_, 0);
lean_inc_ref(v_rpcEncode_776_);
lean_dec_ref(v_inst_771_);
v___x_648__overap_777_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_772_, v_rpcEncode_776_, v_a_774_);
v___x_778_ = lean_apply_1(v___x_648__overap_777_, v___y_775_);
v_fst_779_ = lean_ctor_get(v___x_778_, 0);
v_snd_780_ = lean_ctor_get(v___x_778_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___x_778_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_inc(v_fst_779_);
lean_dec(v___x_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v___x_773_, v_fst_779_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_snd_780_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(lean_object* v___f_789_, lean_object* v_inst_790_, lean_object* v___x_791_, lean_object* v_a_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v___f_789_, v_a_792_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___x_791_);
lean_dec_ref(v_inst_790_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_803_; lean_object* v_rpcDecode_804_; lean_object* v___x_661__overap_805_; lean_object* v___x_806_; 
v_a_803_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_794_, 1);
v_rpcDecode_804_ = lean_ctor_get(v_inst_790_, 1);
lean_inc_ref(v_rpcDecode_804_);
lean_dec_ref(v_inst_790_);
v___x_661__overap_805_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_791_, v_rpcDecode_804_, v_a_803_);
lean_inc_ref(v___y_793_);
v___x_806_ = lean_apply_1(v___x_661__overap_805_, v___y_793_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed(lean_object* v___f_807_, lean_object* v_inst_808_, lean_object* v___x_809_, lean_object* v_a_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(v___f_807_, v_inst_808_, v___x_809_, v_a_810_, v___y_811_);
lean_dec_ref(v___y_811_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9));
v___x_860_ = l_ReaderT_instMonad___redArg(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22(void){
_start:
{
lean_object* v___x_861_; lean_object* v___f_862_; 
v___x_861_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_862_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_862_, 0, v___x_861_);
return v___f_862_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23(void){
_start:
{
lean_object* v___x_863_; lean_object* v___f_864_; 
v___x_863_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_864_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_864_, 0, v___x_863_);
return v___f_864_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24(void){
_start:
{
lean_object* v___x_865_; lean_object* v___f_866_; 
v___x_865_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_866_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_866_, 0, v___x_865_);
return v___f_866_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25(void){
_start:
{
lean_object* v___x_867_; lean_object* v___f_868_; 
v___x_867_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_868_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_868_, 0, v___x_867_);
return v___f_868_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_870_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_870_, 0, lean_box(0));
lean_closure_set(v___x_870_, 1, lean_box(0));
lean_closure_set(v___x_870_, 2, v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27(void){
_start:
{
lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___f_871_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22);
v___x_872_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___f_871_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_875_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_875_, 0, lean_box(0));
lean_closure_set(v___x_875_, 1, lean_box(0));
lean_closure_set(v___x_875_, 2, v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29(void){
_start:
{
lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___f_876_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25);
v___f_877_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24);
v___f_878_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23);
v___x_879_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28);
v___x_880_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27);
v___x_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___x_879_);
lean_ctor_set(v___x_881_, 2, v___f_878_);
lean_ctor_set(v___x_881_, 3, v___f_877_);
lean_ctor_set(v___x_881_, 4, v___f_876_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_883_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_883_, 0, lean_box(0));
lean_closure_set(v___x_883_, 1, lean_box(0));
lean_closure_set(v___x_883_, 2, v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30);
v___x_885_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg(lean_object* v_inst_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___x_895_; 
v___x_889_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_890_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20));
lean_inc_ref(v_inst_888_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0), 5, 3);
lean_closure_set(v___f_891_, 0, v_inst_888_);
lean_closure_set(v___f_891_, 1, v___x_889_);
lean_closure_set(v___f_891_, 2, v___x_890_);
v___x_892_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31);
v___f_893_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32));
v___f_894_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_894_, 0, v___f_893_);
lean_closure_set(v___f_894_, 1, v_inst_888_);
lean_closure_set(v___f_894_, 2, v___x_892_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___f_891_);
lean_ctor_set(v___x_895_, 1, v___f_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable(lean_object* v_00_u03b1_896_, lean_object* v_inst_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object* v_s_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_out_909_; lean_object* v_tagStack_910_; lean_object* v_column_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_923_; 
v_out_909_ = lean_ctor_get(v___y_908_, 0);
v_tagStack_910_ = lean_ctor_get(v___y_908_, 1);
v_column_911_ = lean_ctor_get(v___y_908_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v___y_908_);
if (v_isSharedCheck_923_ == 0)
{
v___x_913_ = v___y_908_;
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_column_911_);
lean_inc(v_tagStack_910_);
lean_inc(v_out_909_);
lean_dec(v___y_908_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_915_ = lean_box(0);
lean_inc_ref(v_s_907_);
v___x_916_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_907_, v_out_909_);
v___x_917_ = lean_string_length(v_s_907_);
lean_dec_ref(v_s_907_);
v___x_918_ = lean_nat_add(v_column_911_, v___x_917_);
lean_dec(v_column_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 2, v___x_918_);
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_920_ = v___x_913_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_tagStack_910_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v___x_918_);
v___x_920_ = v_reuseFailAlloc_922_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_915_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t v___x_924_, lean_object* v_s_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = lean_string_push(v_s_925_, v___x_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object* v___x_927_, lean_object* v_s_928_){
_start:
{
uint32_t v___x_834__boxed_929_; lean_object* v_res_930_; 
v___x_834__boxed_929_ = lean_unbox_uint32(v___x_927_);
lean_dec(v___x_927_);
v_res_930_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_834__boxed_929_, v_s_928_);
return v_res_930_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_932_; lean_object* v___x_933_; 
v___x_932_ = 32;
v___x_933_ = lean_box_uint32(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1(void){
_start:
{
lean_object* v___x_934_; lean_object* v___f_935_; 
v___x_934_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
v___f_935_ = lean_alloc_closure((void*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed), 2, 1);
lean_closure_set(v___f_935_, 0, v___x_934_);
return v___f_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object* v_indent_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_out_938_; lean_object* v_tagStack_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_952_; 
v_out_938_ = lean_ctor_get(v___y_937_, 0);
v_tagStack_939_ = lean_ctor_get(v___y_937_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___y_937_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___y_937_, 2);
lean_dec(v_unused_953_);
v___x_941_ = v___y_937_;
v_isShared_942_ = v_isSharedCheck_952_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_tagStack_939_);
lean_inc(v_out_938_);
lean_dec(v___y_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_952_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_943_ = lean_box(0);
v___x_944_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
v___f_945_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
lean_inc(v_indent_936_);
v___x_946_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_945_, v_indent_936_, v___x_944_);
v___x_947_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_946_, v_out_938_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 2, v_indent_936_);
lean_ctor_set(v___x_941_, 0, v___x_947_);
v___x_949_ = v___x_941_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_tagStack_939_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_indent_936_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_943_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object* v_____do__lift_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_column_956_; lean_object* v___x_957_; 
v_column_956_ = lean_ctor_get(v_____do__lift_954_, 2);
lean_inc(v_column_956_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_column_956_);
lean_ctor_set(v___x_957_, 1, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object* v_____do__lift_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_958_, v___y_959_);
lean_dec_ref(v_____do__lift_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object* v_n_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_out_963_; lean_object* v_tagStack_964_; lean_object* v_column_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_978_; 
v_out_963_ = lean_ctor_get(v___y_962_, 0);
v_tagStack_964_ = lean_ctor_get(v___y_962_, 1);
v_column_965_ = lean_ctor_get(v___y_962_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v___y_962_);
if (v_isSharedCheck_978_ == 0)
{
v___x_967_ = v___y_962_;
v_isShared_968_ = v_isSharedCheck_978_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_column_965_);
lean_inc(v_tagStack_964_);
lean_inc(v_out_963_);
lean_dec(v___y_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_978_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_969_ = lean_box(0);
v___x_970_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_965_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_column_965_);
lean_ctor_set(v___x_971_, 1, v_out_963_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_n_961_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_tagStack_964_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_973_);
lean_ctor_set(v___x_967_, 0, v___x_970_);
v___x_975_ = v___x_967_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_column_965_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_969_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object* v_acc_979_, lean_object* v_x_980_){
_start:
{
lean_object* v_snd_981_; lean_object* v_fst_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_992_; 
v_snd_981_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_snd_981_);
v_fst_982_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_fst_982_);
lean_dec_ref(v_x_980_);
v_fst_983_ = lean_ctor_get(v_snd_981_, 0);
v_snd_984_ = lean_ctor_get(v_snd_981_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_snd_981_);
if (v_isSharedCheck_992_ == 0)
{
v___x_986_ = v_snd_981_;
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_983_);
lean_dec(v_snd_981_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_fst_983_);
lean_ctor_set(v___x_986_, 0, v_fst_982_);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_982_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_fst_983_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_984_, v___x_989_, v_acc_979_);
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object* v___f_995_, lean_object* v_n_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_out_998_; lean_object* v_tagStack_999_; lean_object* v_column_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1013_; 
v_out_998_ = lean_ctor_get(v___y_997_, 0);
v_tagStack_999_ = lean_ctor_get(v___y_997_, 1);
v_column_1000_ = lean_ctor_get(v___y_997_, 2);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___y_997_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1002_ = v___y_997_;
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_column_1000_);
lean_inc(v_tagStack_999_);
lean_inc(v_out_998_);
lean_dec(v___y_997_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_out_x27_1008_; lean_object* v___x_1010_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_n_996_);
lean_inc(v_tagStack_999_);
v___x_1006_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_999_, v_tagStack_999_, v_n_996_, v___x_1005_);
v___x_1007_ = l_List_drop___redArg(v_n_996_, v_tagStack_999_);
lean_dec(v_tagStack_999_);
v_out_x27_1008_ = l_List_foldl___redArg(v___f_995_, v_out_998_, v___x_1006_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___x_1007_);
lean_ctor_set(v___x_1002_, 0, v_out_x27_1008_);
v___x_1010_ = v___x_1002_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_out_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_column_1000_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1004_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_zero_1036_; uint8_t v_isZero_1037_; 
v_zero_1036_ = lean_unsigned_to_nat(0u);
v_isZero_1037_ = lean_nat_dec_eq(v_x_1034_, v_zero_1036_);
if (v_isZero_1037_ == 1)
{
lean_dec(v_x_1034_);
return v_x_1035_;
}
else
{
uint32_t v___x_1038_; lean_object* v_one_1039_; lean_object* v_n_1040_; lean_object* v___x_1041_; 
v___x_1038_ = 32;
v_one_1039_ = lean_unsigned_to_nat(1u);
v_n_1040_ = lean_nat_sub(v_x_1034_, v_one_1039_);
lean_dec(v_x_1034_);
v___x_1041_ = lean_string_push(v_x_1035_, v___x_1038_);
v_x_1034_ = v_n_1040_;
v_x_1035_ = v___x_1041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object* v_fla_1043_, uint8_t v_flb_1044_, lean_object* v_tail_1045_, lean_object* v_is_x27_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1047_, 0, v_fla_1043_);
lean_ctor_set(v___x_1047_, 1, v_is_x27_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*2, v_flb_1044_);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_tail_1045_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object* v_fla_1049_, lean_object* v_flb_1050_, lean_object* v_tail_1051_, lean_object* v_is_x27_1052_){
_start:
{
uint8_t v_flb_6280__boxed_1053_; lean_object* v_res_1054_; 
v_flb_6280__boxed_1053_ = lean_unbox(v_flb_1050_);
v_res_1054_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1049_, v_flb_6280__boxed_1053_, v_tail_1051_, v_is_x27_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t v_flb_1055_, lean_object* v_items_1056_, lean_object* v_gs_1057_, lean_object* v_w_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___y_1061_; lean_object* v_column_1066_; uint8_t v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v_g_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_r_1074_; lean_object* v___y_1076_; uint8_t v_foundLine_1081_; lean_object* v_space_1082_; uint8_t v___x_1083_; 
v_column_1066_ = lean_ctor_get(v___y_1059_, 2);
v___x_1067_ = 0;
v___x_1068_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1055_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1069_, 0, v___x_1068_);
lean_inc(v_items_1056_);
v_g_1070_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1070_, 0, v___x_1069_);
lean_ctor_set(v_g_1070_, 1, v_items_1056_);
lean_ctor_set_uint8(v_g_1070_, sizeof(void*)*2, v_flb_1055_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_g_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_nat_sub(v_w_1058_, v_column_1066_);
lean_inc(v___x_1073_);
lean_inc(v_column_1066_);
v_r_1074_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1072_, v_column_1066_, v___x_1073_);
v_foundLine_1081_ = lean_ctor_get_uint8(v_r_1074_, sizeof(void*)*1);
v_space_1082_ = lean_ctor_get(v_r_1074_, 0);
v___x_1083_ = lean_nat_dec_lt(v___x_1073_, v_space_1082_);
if (v___x_1083_ == 0)
{
if (v_foundLine_1081_ == 0)
{
lean_object* v___x_1084_; lean_object* v_r_u2082_1085_; uint8_t v_foundLine_1086_; uint8_t v_foundFlattenedHardLine_1087_; lean_object* v_space_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v___x_1084_ = lean_nat_sub(v___x_1073_, v_space_1082_);
lean_inc(v_column_1066_);
lean_inc(v_gs_1057_);
v_r_u2082_1085_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1057_, v_column_1066_, v___x_1084_);
v_foundLine_1086_ = lean_ctor_get_uint8(v_r_u2082_1085_, sizeof(void*)*1);
v_foundFlattenedHardLine_1087_ = lean_ctor_get_uint8(v_r_u2082_1085_, sizeof(void*)*1 + 1);
v_space_1088_ = lean_ctor_get(v_r_u2082_1085_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_r_u2082_1085_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v_r_u2082_1085_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_space_1088_);
lean_dec(v_r_u2082_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_nat_add(v_space_1082_, v_space_1088_);
lean_dec(v_space_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*1, v_foundLine_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1087_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v___y_1076_ = v___x_1094_;
goto v___jp_1075_;
}
}
}
else
{
lean_inc_ref(v_r_1074_);
v___y_1076_ = v_r_1074_;
goto v___jp_1075_;
}
}
else
{
lean_inc_ref(v_r_1074_);
v___y_1076_ = v_r_1074_;
goto v___jp_1075_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1062_, 0, v___y_1061_);
v___x_1063_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_items_1056_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*2, v_flb_1055_);
v___x_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_gs_1057_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___y_1059_);
return v___x_1065_;
}
v___jp_1075_:
{
uint8_t v_foundFlattenedHardLine_1077_; 
v_foundFlattenedHardLine_1077_ = lean_ctor_get_uint8(v_r_1074_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1074_);
if (v_foundFlattenedHardLine_1077_ == 0)
{
lean_object* v_space_1078_; uint8_t v___x_1079_; 
v_space_1078_ = lean_ctor_get(v___y_1076_, 0);
lean_inc(v_space_1078_);
lean_dec_ref(v___y_1076_);
v___x_1079_ = lean_nat_dec_le(v_space_1078_, v___x_1073_);
lean_dec(v___x_1073_);
lean_dec(v_space_1078_);
v___y_1061_ = v___x_1079_;
goto v___jp_1060_;
}
else
{
uint8_t v___x_1080_; 
lean_dec_ref(v___y_1076_);
lean_dec(v___x_1073_);
v___x_1080_ = 0;
v___y_1061_ = v___x_1080_;
goto v___jp_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object* v_flb_1097_, lean_object* v_items_1098_, lean_object* v_gs_1099_, lean_object* v_w_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_flb_boxed_1102_; lean_object* v_res_1103_; 
v_flb_boxed_1102_ = lean_unbox(v_flb_1097_);
v_res_1103_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_1102_, v_items_1098_, v_gs_1099_, v_w_1100_, v___y_1101_);
lean_dec(v_w_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
return v_x_1104_;
}
else
{
lean_object* v_head_1106_; lean_object* v_snd_1107_; lean_object* v_tail_1108_; lean_object* v_fst_1109_; lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v_head_1106_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_head_1106_);
v_snd_1107_ = lean_ctor_get(v_head_1106_, 1);
lean_inc(v_snd_1107_);
v_tail_1108_ = lean_ctor_get(v_x_1105_, 1);
lean_inc(v_tail_1108_);
lean_dec_ref_known(v_x_1105_, 2);
v_fst_1109_ = lean_ctor_get(v_head_1106_, 0);
lean_inc(v_fst_1109_);
lean_dec(v_head_1106_);
v_fst_1110_ = lean_ctor_get(v_snd_1107_, 0);
v_snd_1111_ = lean_ctor_get(v_snd_1107_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_snd_1107_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v_snd_1107_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_snd_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_fst_1110_);
lean_ctor_set(v___x_1113_, 0, v_fst_1109_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_fst_1109_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_fst_1110_);
v___x_1116_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_1111_, v___x_1116_, v_x_1104_);
v_x_1104_ = v___x_1117_;
v_x_1105_ = v_tail_1108_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_1123_ = l_instInhabitedOfMonad___redArg(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object* v_msg_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_6185__overap_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0, &l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once, _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
v___x_6185__overap_1127_ = lean_panic_fn_borrowed(v___x_1126_, v_msg_1124_);
v___x_1128_ = lean_apply_1(v___x_6185__overap_1127_, v___y_1125_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1131_ = lean_string_length(v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object* v_w_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___y_1135_);
return v___x_1137_;
}
else
{
lean_object* v_head_1138_; lean_object* v_items_1139_; 
v_head_1138_ = lean_ctor_get(v_x_1134_, 0);
v_items_1139_ = lean_ctor_get(v_head_1138_, 1);
lean_inc(v_items_1139_);
if (lean_obj_tag(v_items_1139_) == 0)
{
lean_object* v_tail_1140_; 
v_tail_1140_ = lean_ctor_get(v_x_1134_, 1);
lean_inc(v_tail_1140_);
lean_dec_ref_known(v_x_1134_, 2);
v_x_1134_ = v_tail_1140_;
goto _start;
}
else
{
lean_object* v_head_1142_; lean_object* v_tail_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1494_; 
lean_inc(v_head_1138_);
v_head_1142_ = lean_ctor_get(v_items_1139_, 0);
lean_inc(v_head_1142_);
v_tail_1143_ = lean_ctor_get(v_x_1134_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_x_1134_, 0);
lean_dec(v_unused_1495_);
v___x_1145_ = v_x_1134_;
v_isShared_1146_ = v_isSharedCheck_1494_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_tail_1143_);
lean_dec(v_x_1134_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1494_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_fla_1147_; uint8_t v_flb_1148_; lean_object* v_tail_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1492_; 
v_fla_1147_ = lean_ctor_get(v_head_1138_, 0);
lean_inc(v_fla_1147_);
v_flb_1148_ = lean_ctor_get_uint8(v_head_1138_, sizeof(void*)*2);
lean_dec(v_head_1138_);
v_tail_1149_ = lean_ctor_get(v_items_1139_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_items_1139_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_items_1139_, 0);
lean_dec(v_unused_1493_);
v___x_1151_ = v_items_1139_;
v_isShared_1152_ = v_isSharedCheck_1492_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_tail_1149_);
lean_dec(v_items_1139_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1492_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_f_1153_; lean_object* v_indent_1154_; lean_object* v_activeTags_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1491_; 
v_f_1153_ = lean_ctor_get(v_head_1142_, 0);
v_indent_1154_ = lean_ctor_get(v_head_1142_, 1);
v_activeTags_1155_ = lean_ctor_get(v_head_1142_, 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_head_1142_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1157_ = v_head_1142_;
v_isShared_1158_ = v_isSharedCheck_1491_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_activeTags_1155_);
lean_inc(v_indent_1154_);
lean_inc(v_f_1153_);
lean_dec(v_head_1142_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1491_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___y_1200_; 
switch(lean_obj_tag(v_f_1153_))
{
case 0:
{
lean_object* v_out_1217_; lean_object* v_tagStack_1218_; lean_object* v_column_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1232_; 
lean_del_object(v___x_1157_);
lean_dec(v_indent_1154_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1145_);
v_out_1217_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1218_ = lean_ctor_get(v___y_1135_, 1);
v_column_1219_ = lean_ctor_get(v___y_1135_, 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1221_ = v___y_1135_;
v_isShared_1222_ = v_isSharedCheck_1232_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_column_1219_);
lean_inc(v_tagStack_1218_);
lean_inc(v_out_1217_);
lean_dec(v___y_1135_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1232_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_out_x27_1226_; lean_object* v___x_1228_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1218_);
v___x_1224_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1218_, v_tagStack_1218_, v_activeTags_1155_, v___x_1223_);
v___x_1225_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1218_);
lean_dec(v_tagStack_1218_);
v_out_x27_1226_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1217_, v___x_1224_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1225_);
lean_ctor_set(v___x_1221_, 0, v_out_x27_1226_);
v___x_1228_ = v___x_1221_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_out_x27_1226_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_column_1219_);
v___x_1228_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1229_;
v___y_1135_ = v___x_1228_;
goto _start;
}
}
}
case 1:
{
lean_del_object(v___x_1157_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1145_);
if (v_flb_1148_ == 0)
{
uint8_t v___x_1233_; 
v___x_1233_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1147_);
if (v___x_1233_ == 0)
{
lean_object* v_out_1234_; lean_object* v_tagStack_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1252_; 
v_out_1234_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1235_ = lean_ctor_get(v___y_1135_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___y_1135_, 2);
lean_dec(v_unused_1253_);
v___x_1237_ = v___y_1135_;
v_isShared_1238_ = v_isSharedCheck_1252_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_tagStack_1235_);
lean_inc(v_out_1234_);
lean_dec(v___y_1135_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1252_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_out_x27_1246_; lean_object* v___x_1248_; 
v___x_1239_ = l_Int_toNat(v_indent_1154_);
lean_dec(v_indent_1154_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1239_);
v___x_1241_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1239_, v___x_1240_);
v___x_1242_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1241_, v_out_1234_);
v___x_1243_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1235_);
v___x_1244_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1235_, v_tagStack_1235_, v_activeTags_1155_, v___x_1243_);
v___x_1245_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1235_);
lean_dec(v_tagStack_1235_);
v_out_x27_1246_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1242_, v___x_1244_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 2, v___x_1239_);
lean_ctor_set(v___x_1237_, 1, v___x_1245_);
lean_ctor_set(v___x_1237_, 0, v_out_x27_1246_);
v___x_1248_ = v___x_1237_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_out_x27_1246_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v___x_1239_);
v___x_1248_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1249_;
v___y_1135_ = v___x_1248_;
goto _start;
}
}
}
else
{
lean_object* v_out_1254_; lean_object* v_tagStack_1255_; lean_object* v_column_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_indent_1154_);
v_out_1254_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1255_ = lean_ctor_get(v___y_1135_, 1);
v_column_1256_ = lean_ctor_get(v___y_1135_, 2);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1258_ = v___y_1135_;
v_isShared_1259_ = v_isSharedCheck_1273_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_column_1256_);
lean_inc(v_tagStack_1255_);
lean_inc(v_out_1254_);
lean_dec(v___y_1135_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1273_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_out_x27_1267_; lean_object* v___x_1269_; 
v___x_1260_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1261_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1260_, v_out_1254_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v_column_1256_, v___x_1262_);
lean_dec(v_column_1256_);
v___x_1264_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1255_);
v___x_1265_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1255_, v_tagStack_1255_, v_activeTags_1155_, v___x_1264_);
v___x_1266_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1255_);
lean_dec(v_tagStack_1255_);
v_out_x27_1267_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1261_, v___x_1265_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 2, v___x_1263_);
lean_ctor_set(v___x_1258_, 1, v___x_1266_);
lean_ctor_set(v___x_1258_, 0, v_out_x27_1267_);
v___x_1269_ = v___x_1258_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_out_x27_1267_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v___x_1263_);
v___x_1269_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1270_;
v___y_1135_ = v___x_1269_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = l_Int_toNat(v_indent_1154_);
lean_dec(v_indent_1154_);
v___x_1275_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1147_);
lean_dec(v_fla_1147_);
if (v___x_1275_ == 0)
{
lean_object* v_out_1276_; lean_object* v_tagStack_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1295_; 
v_out_1276_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1277_ = lean_ctor_get(v___y_1135_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___y_1135_, 2);
lean_dec(v_unused_1296_);
v___x_1279_ = v___y_1135_;
v_isShared_1280_ = v_isSharedCheck_1295_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_tagStack_1277_);
lean_inc(v_out_1276_);
lean_dec(v___y_1135_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1295_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_out_x27_1287_; lean_object* v___x_1289_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1274_);
v___x_1282_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1274_, v___x_1281_);
v___x_1283_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1282_, v_out_1276_);
v___x_1284_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1277_);
v___x_1285_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1277_, v_tagStack_1277_, v_activeTags_1155_, v___x_1284_);
v___x_1286_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1277_);
lean_dec(v_tagStack_1277_);
v_out_x27_1287_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1283_, v___x_1285_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 2, v___x_1274_);
lean_ctor_set(v___x_1279_, 1, v___x_1286_);
lean_ctor_set(v___x_1279_, 0, v_out_x27_1287_);
v___x_1289_ = v___x_1279_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_out_x27_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v___x_1274_);
v___x_1289_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v_fst_1291_; lean_object* v_snd_1292_; 
v___x_1290_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1148_, v_tail_1149_, v_tail_1143_, v_w_1133_, v___x_1289_);
v_fst_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_fst_1291_);
v_snd_1292_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___x_1290_);
v_x_1134_ = v_fst_1291_;
v___y_1135_ = v_snd_1292_;
goto _start;
}
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_fst_1301_; 
v___x_1297_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1298_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
v___x_1299_ = lean_nat_sub(v_w_1133_, v___x_1298_);
lean_inc(v_tail_1143_);
lean_inc(v_tail_1149_);
v___x_1300_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1148_, v_tail_1149_, v_tail_1143_, v___x_1299_, v___y_1135_);
lean_dec(v___x_1299_);
v_fst_1301_ = lean_ctor_get(v___x_1300_, 0);
if (lean_obj_tag(v_fst_1301_) == 1)
{
lean_object* v_head_1302_; lean_object* v_snd_1303_; lean_object* v_fla_1304_; uint8_t v___x_1305_; 
lean_inc_ref(v_fst_1301_);
v_head_1302_ = lean_ctor_get(v_fst_1301_, 0);
v_snd_1303_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___x_1300_);
v_fla_1304_ = lean_ctor_get(v_head_1302_, 0);
v___x_1305_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1304_);
if (v___x_1305_ == 0)
{
lean_object* v_out_1306_; lean_object* v_tagStack_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref_known(v_fst_1301_, 2);
v_out_1306_ = lean_ctor_get(v_snd_1303_, 0);
v_tagStack_1307_ = lean_ctor_get(v_snd_1303_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_snd_1303_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_snd_1303_, 2);
lean_dec(v_unused_1326_);
v___x_1309_ = v_snd_1303_;
v_isShared_1310_ = v_isSharedCheck_1325_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_tagStack_1307_);
lean_inc(v_out_1306_);
lean_dec(v_snd_1303_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1325_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_out_x27_1317_; lean_object* v___x_1319_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1274_);
v___x_1312_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1274_, v___x_1311_);
v___x_1313_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1312_, v_out_1306_);
v___x_1314_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1307_);
v___x_1315_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1307_, v_tagStack_1307_, v_activeTags_1155_, v___x_1314_);
v___x_1316_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1307_);
lean_dec(v_tagStack_1307_);
v_out_x27_1317_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1313_, v___x_1315_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 2, v___x_1274_);
lean_ctor_set(v___x_1309_, 1, v___x_1316_);
lean_ctor_set(v___x_1309_, 0, v_out_x27_1317_);
v___x_1319_ = v___x_1309_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_out_x27_1317_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v___x_1274_);
v___x_1319_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; 
v___x_1320_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1148_, v_tail_1149_, v_tail_1143_, v_w_1133_, v___x_1319_);
v_fst_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_fst_1321_);
v_snd_1322_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_snd_1322_);
lean_dec_ref(v___x_1320_);
v_x_1134_ = v_fst_1321_;
v___y_1135_ = v_snd_1322_;
goto _start;
}
}
}
else
{
lean_object* v_out_1327_; lean_object* v_tagStack_1328_; lean_object* v_column_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v___x_1274_);
lean_dec(v_tail_1149_);
lean_dec(v_tail_1143_);
v_out_1327_ = lean_ctor_get(v_snd_1303_, 0);
v_tagStack_1328_ = lean_ctor_get(v_snd_1303_, 1);
v_column_1329_ = lean_ctor_get(v_snd_1303_, 2);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_snd_1303_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1331_ = v_snd_1303_;
v_isShared_1332_ = v_isSharedCheck_1344_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_column_1329_);
lean_inc(v_tagStack_1328_);
lean_inc(v_out_1327_);
lean_dec(v_snd_1303_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1344_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_out_x27_1339_; lean_object* v___x_1341_; 
v___x_1333_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1297_, v_out_1327_);
v___x_1334_ = lean_unsigned_to_nat(1u);
v___x_1335_ = lean_nat_add(v_column_1329_, v___x_1334_);
lean_dec(v_column_1329_);
v___x_1336_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1328_);
v___x_1337_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1328_, v_tagStack_1328_, v_activeTags_1155_, v___x_1336_);
v___x_1338_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1328_);
lean_dec(v_tagStack_1328_);
v_out_x27_1339_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1333_, v___x_1337_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 2, v___x_1335_);
lean_ctor_set(v___x_1331_, 1, v___x_1338_);
lean_ctor_set(v___x_1331_, 0, v_out_x27_1339_);
v___x_1341_ = v___x_1331_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_out_x27_1339_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v___x_1335_);
v___x_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
v_x_1134_ = v_fst_1301_;
v___y_1135_ = v___x_1341_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v___x_1274_);
lean_dec(v_activeTags_1155_);
lean_dec(v_tail_1149_);
lean_dec(v_tail_1143_);
v_snd_1345_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1345_);
lean_dec_ref(v___x_1300_);
v___x_1346_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2));
v___x_1347_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_1346_, v_snd_1345_);
return v___x_1347_;
}
}
}
}
case 2:
{
uint8_t v_force_1348_; uint8_t v___x_1349_; 
lean_del_object(v___x_1157_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1145_);
v_force_1348_ = lean_ctor_get_uint8(v_f_1153_, 0);
lean_dec_ref_known(v_f_1153_, 0);
v___x_1349_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1147_);
if (v___x_1349_ == 0)
{
v___y_1200_ = v___x_1349_;
goto v___jp_1199_;
}
else
{
if (v_force_1348_ == 0)
{
v___y_1200_ = v___x_1349_;
goto v___jp_1199_;
}
else
{
goto v___jp_1159_;
}
}
}
case 3:
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1145_);
v_a_1350_ = lean_ctor_get(v_f_1153_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_f_1153_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1352_ = v_f_1153_;
v_isShared_1353_ = v_isSharedCheck_1413_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v_f_1153_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1413_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
uint32_t v___x_1354_; lean_object* v_p_1355_; lean_object* v___x_1356_; uint8_t v_decide_1357_; 
v___x_1354_ = 10;
lean_inc_ref(v_a_1350_);
v_p_1355_ = lean_string_posof(v_a_1350_, v___x_1354_);
v___x_1356_ = lean_string_utf8_byte_size(v_a_1350_);
v_decide_1357_ = lean_nat_dec_eq(v_p_1355_, v___x_1356_);
if (v_decide_1357_ == 0)
{
lean_object* v_out_1358_; lean_object* v_tagStack_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1392_; 
v_out_1358_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1359_ = lean_ctor_get(v___y_1135_, 1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___y_1135_, 2);
lean_dec(v_unused_1393_);
v___x_1361_ = v___y_1135_;
v_isShared_1362_ = v_isSharedCheck_1392_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_tagStack_1359_);
lean_inc(v_out_1358_);
lean_dec(v___y_1135_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1392_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_string_utf8_extract(v_a_1350_, v___x_1363_, v_p_1355_);
v___x_1365_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1364_, v_out_1358_);
v___x_1366_ = l_Int_toNat(v_indent_1154_);
v___x_1367_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1366_);
v___x_1368_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1366_, v___x_1367_);
v___x_1369_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1368_, v___x_1365_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 2, v___x_1366_);
lean_ctor_set(v___x_1361_, 0, v___x_1369_);
v___x_1371_ = v___x_1361_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_tagStack_1359_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v___x_1366_);
v___x_1371_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_string_utf8_next(v_a_1350_, v_p_1355_);
lean_dec(v_p_1355_);
v___x_1373_ = lean_string_utf8_extract(v_a_1350_, v___x_1372_, v___x_1356_);
lean_dec(v___x_1372_);
lean_dec_ref(v_a_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1373_);
v___x_1375_ = v___x_1352_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1375_);
v___x_1377_ = v___x_1157_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_indent_1154_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_activeTags_1155_);
v___x_1377_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v_is_1379_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1377_);
v_is_1379_ = v___x_1151_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_tail_1149_);
v_is_1379_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_box(1);
v___x_1381_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1147_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v_fst_1383_; lean_object* v_snd_1384_; 
lean_dec(v_fla_1147_);
v___x_1382_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1148_, v_is_1379_, v_tail_1143_, v_w_1133_, v___x_1371_);
v_fst_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_fst_1383_);
v_snd_1384_ = lean_ctor_get(v___x_1382_, 1);
lean_inc(v_snd_1384_);
lean_dec_ref(v___x_1382_);
v_x_1134_ = v_fst_1383_;
v___y_1135_ = v_snd_1384_;
goto _start;
}
else
{
lean_object* v___x_1386_; 
v___x_1386_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_is_1379_);
v_x_1134_ = v___x_1386_;
v___y_1135_ = v___x_1371_;
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
lean_object* v_out_1394_; lean_object* v_tagStack_1395_; lean_object* v_column_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_p_1355_);
lean_del_object(v___x_1352_);
lean_del_object(v___x_1157_);
lean_dec(v_indent_1154_);
lean_del_object(v___x_1151_);
v_out_1394_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1395_ = lean_ctor_get(v___y_1135_, 1);
v_column_1396_ = lean_ctor_get(v___y_1135_, 2);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1398_ = v___y_1135_;
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_column_1396_);
lean_inc(v_tagStack_1395_);
lean_inc(v_out_1394_);
lean_dec(v___y_1135_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_out_x27_1406_; lean_object* v___x_1408_; 
lean_inc_ref(v_a_1350_);
v___x_1400_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_1350_, v_out_1394_);
v___x_1401_ = lean_string_length(v_a_1350_);
lean_dec_ref(v_a_1350_);
v___x_1402_ = lean_nat_add(v_column_1396_, v___x_1401_);
lean_dec(v_column_1396_);
v___x_1403_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1395_);
v___x_1404_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1395_, v_tagStack_1395_, v_activeTags_1155_, v___x_1403_);
v___x_1405_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1395_);
lean_dec(v_tagStack_1395_);
v_out_x27_1406_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1400_, v___x_1404_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 2, v___x_1402_);
lean_ctor_set(v___x_1398_, 1, v___x_1405_);
lean_ctor_set(v___x_1398_, 0, v_out_x27_1406_);
v___x_1408_ = v___x_1398_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_out_x27_1406_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v___x_1402_);
v___x_1408_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1409_;
v___y_1135_ = v___x_1408_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1414_; lean_object* v_f_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_del_object(v___x_1145_);
v_indent_1414_ = lean_ctor_get(v_f_1153_, 0);
lean_inc(v_indent_1414_);
v_f_1415_ = lean_ctor_get(v_f_1153_, 1);
lean_inc(v_f_1415_);
lean_dec_ref_known(v_f_1153_, 2);
v___x_1416_ = lean_int_add(v_indent_1154_, v_indent_1414_);
lean_dec(v_indent_1414_);
lean_dec(v_indent_1154_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v___x_1416_);
lean_ctor_set(v___x_1157_, 0, v_f_1415_);
v___x_1418_ = v___x_1157_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_f_1415_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_activeTags_1155_);
v___x_1418_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1418_);
v___x_1420_ = v___x_1151_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_tail_1149_);
v___x_1420_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v___x_1420_);
v_x_1134_ = v___x_1421_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1425_; lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_a_1425_ = lean_ctor_get(v_f_1153_, 0);
lean_inc(v_a_1425_);
v_a_1426_ = lean_ctor_get(v_f_1153_, 1);
lean_inc(v_a_1426_);
lean_dec_ref_known(v_f_1153_, 2);
v___x_1427_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1154_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 2, v___x_1427_);
lean_ctor_set(v___x_1157_, 0, v_a_1425_);
v___x_1429_ = v___x_1157_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1425_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_indent_1154_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1426_);
lean_ctor_set(v___x_1430_, 1, v_indent_1154_);
lean_ctor_set(v___x_1430_, 2, v_activeTags_1155_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1430_);
v___x_1432_ = v___x_1151_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_tail_1149_);
v___x_1432_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1432_);
lean_ctor_set(v___x_1145_, 0, v___x_1429_);
v___x_1434_ = v___x_1145_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v___x_1434_);
v_x_1134_ = v___x_1435_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1440_; uint8_t v_behavior_1441_; uint8_t v___x_1442_; 
lean_del_object(v___x_1145_);
v_a_1440_ = lean_ctor_get(v_f_1153_, 0);
lean_inc(v_a_1440_);
v_behavior_1441_ = lean_ctor_get_uint8(v_f_1153_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1153_, 1);
v___x_1442_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1147_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_a_1440_);
v___x_1444_ = v___x_1157_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1440_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_indent_1154_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_activeTags_1155_);
v___x_1444_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_box(0);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___x_1445_);
lean_ctor_set(v___x_1151_, 0, v___x_1444_);
v___x_1447_ = v___x_1151_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_fst_1450_; lean_object* v_snd_1451_; 
v___x_1448_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v___x_1449_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_1441_, v___x_1447_, v___x_1448_, v_w_1133_, v___y_1135_);
v_fst_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_fst_1450_);
v_snd_1451_ = lean_ctor_get(v___x_1449_, 1);
lean_inc(v_snd_1451_);
lean_dec_ref(v___x_1449_);
v_x_1134_ = v_fst_1450_;
v___y_1135_ = v_snd_1451_;
goto _start;
}
}
}
else
{
lean_object* v___x_1456_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_a_1440_);
v___x_1456_ = v___x_1157_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1440_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_indent_1154_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_activeTags_1155_);
v___x_1456_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1456_);
v___x_1458_ = v___x_1151_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_tail_1149_);
v___x_1458_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v___x_1458_);
v_x_1134_ = v___x_1459_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1463_; lean_object* v_a_1464_; lean_object* v_out_1465_; lean_object* v_tagStack_1466_; lean_object* v_column_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1490_; 
v_a_1463_ = lean_ctor_get(v_f_1153_, 0);
lean_inc(v_a_1463_);
v_a_1464_ = lean_ctor_get(v_f_1153_, 1);
lean_inc(v_a_1464_);
lean_dec_ref_known(v_f_1153_, 2);
v_out_1465_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1466_ = lean_ctor_get(v___y_1135_, 1);
v_column_1467_ = lean_ctor_get(v___y_1135_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1469_ = v___y_1135_;
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_column_1467_);
lean_inc(v_tagStack_1466_);
lean_inc(v_out_1465_);
lean_dec(v___y_1135_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1471_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_1467_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_column_1467_);
lean_ctor_set(v___x_1472_, 1, v_out_1465_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1463_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_tagStack_1466_);
lean_ctor_set(v___x_1151_, 0, v___x_1473_);
v___x_1475_ = v___x_1151_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_tagStack_1466_);
v___x_1475_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1475_);
lean_ctor_set(v___x_1469_, 0, v___x_1471_);
v___x_1477_ = v___x_1469_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_column_1467_);
v___x_1477_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_add(v_activeTags_1155_, v___x_1478_);
lean_dec(v_activeTags_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 2, v___x_1479_);
lean_ctor_set(v___x_1157_, 0, v_a_1464_);
v___x_1481_ = v___x_1157_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1464_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_indent_1154_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_tail_1149_);
lean_ctor_set(v___x_1145_, 0, v___x_1481_);
v___x_1483_ = v___x_1145_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_tail_1149_);
v___x_1483_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v___x_1483_);
v_x_1134_ = v___x_1484_;
v___y_1135_ = v___x_1477_;
goto _start;
}
}
}
}
}
}
}
v___jp_1159_:
{
lean_object* v_out_1160_; lean_object* v_tagStack_1161_; lean_object* v_column_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1198_; 
v_out_1160_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1161_ = lean_ctor_get(v___y_1135_, 1);
v_column_1162_ = lean_ctor_get(v___y_1135_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1164_ = v___y_1135_;
v_isShared_1165_ = v_isSharedCheck_1198_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_column_1162_);
lean_inc(v_tagStack_1161_);
lean_inc(v_out_1160_);
lean_dec(v___y_1135_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1198_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
lean_inc(v_column_1162_);
v___x_1166_ = lean_nat_to_int(v_column_1162_);
v___x_1167_ = lean_int_dec_lt(v___x_1166_, v_indent_1154_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_out_x27_1175_; lean_object* v___x_1177_; 
lean_dec(v___x_1166_);
lean_dec(v_column_1162_);
v___x_1168_ = l_Int_toNat(v_indent_1154_);
lean_dec(v_indent_1154_);
v___x_1169_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1168_);
v___x_1170_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1168_, v___x_1169_);
v___x_1171_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1170_, v_out_1160_);
v___x_1172_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1161_);
v___x_1173_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1161_, v_tagStack_1161_, v_activeTags_1155_, v___x_1172_);
v___x_1174_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1161_);
lean_dec(v_tagStack_1161_);
v_out_x27_1175_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1171_, v___x_1173_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 2, v___x_1168_);
lean_ctor_set(v___x_1164_, 1, v___x_1174_);
lean_ctor_set(v___x_1164_, 0, v_out_x27_1175_);
v___x_1177_ = v___x_1164_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_out_x27_1175_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v___x_1168_);
v___x_1177_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1178_;
v___y_1135_ = v___x_1177_;
goto _start;
}
}
else
{
lean_object* v___x_1181_; uint32_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_out_x27_1192_; lean_object* v___x_1194_; 
v___x_1181_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_1182_ = 32;
v___x_1183_ = lean_int_sub(v_indent_1154_, v___x_1166_);
lean_dec(v___x_1166_);
lean_dec(v_indent_1154_);
v___x_1184_ = l_Int_toNat(v___x_1183_);
lean_dec(v___x_1183_);
v___x_1185_ = lean_string_pushn(v___x_1181_, v___x_1182_, v___x_1184_);
lean_inc_ref(v___x_1185_);
v___x_1186_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1185_, v_out_1160_);
v___x_1187_ = lean_string_length(v___x_1185_);
lean_dec_ref(v___x_1185_);
v___x_1188_ = lean_nat_add(v_column_1162_, v___x_1187_);
lean_dec(v_column_1162_);
v___x_1189_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1161_);
v___x_1190_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1161_, v_tagStack_1161_, v_activeTags_1155_, v___x_1189_);
v___x_1191_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1161_);
lean_dec(v_tagStack_1161_);
v_out_x27_1192_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1186_, v___x_1190_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 2, v___x_1188_);
lean_ctor_set(v___x_1164_, 1, v___x_1191_);
lean_ctor_set(v___x_1164_, 0, v_out_x27_1192_);
v___x_1194_ = v___x_1164_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_out_x27_1192_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v___x_1188_);
v___x_1194_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1195_;
v___y_1135_ = v___x_1194_;
goto _start;
}
}
}
}
v___jp_1199_:
{
if (v___y_1200_ == 0)
{
goto v___jp_1159_;
}
else
{
lean_object* v_out_1201_; lean_object* v_tagStack_1202_; lean_object* v_column_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_indent_1154_);
v_out_1201_ = lean_ctor_get(v___y_1135_, 0);
v_tagStack_1202_ = lean_ctor_get(v___y_1135_, 1);
v_column_1203_ = lean_ctor_get(v___y_1135_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___y_1135_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1205_ = v___y_1135_;
v_isShared_1206_ = v_isSharedCheck_1216_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_column_1203_);
lean_inc(v_tagStack_1202_);
lean_inc(v_out_1201_);
lean_dec(v___y_1135_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1216_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_out_x27_1210_; lean_object* v___x_1212_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1155_);
lean_inc(v_tagStack_1202_);
v___x_1208_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1202_, v_tagStack_1202_, v_activeTags_1155_, v___x_1207_);
v___x_1209_ = l_List_drop___redArg(v_activeTags_1155_, v_tagStack_1202_);
lean_dec(v_tagStack_1202_);
v_out_x27_1210_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1201_, v___x_1208_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1209_);
lean_ctor_set(v___x_1205_, 0, v_out_x27_1210_);
v___x_1212_ = v___x_1205_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_out_x27_1210_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_column_1203_);
v___x_1212_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1147_, v_flb_1148_, v_tail_1143_, v_tail_1149_);
v_x_1134_ = v___x_1213_;
v___y_1135_ = v___x_1212_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object* v_w_1496_, lean_object* v_x_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1496_, v_x_1497_, v___y_1498_);
lean_dec(v_w_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object* v_f_1500_, lean_object* v_w_1501_, lean_object* v_indent_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1504_ = lean_box(1);
v___x_1505_ = 0;
v___x_1506_ = lean_nat_to_int(v_indent_1502_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v_f_1500_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1511_, 0, v___x_1504_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*2, v___x_1505_);
v___x_1512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1509_);
v___x_1513_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1501_, v___x_1512_, v___y_1503_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object* v_f_1514_, lean_object* v_w_1515_, lean_object* v_indent_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1514_, v_w_1515_, v_indent_1516_, v___y_1517_);
lean_dec(v_w_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object* v_f_1519_, lean_object* v_indent_1520_, lean_object* v_w_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_snd_1524_; lean_object* v_out_1525_; 
v___x_1522_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1));
v___x_1523_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1519_, v_w_1521_, v_indent_1520_, v___x_1522_);
v_snd_1524_ = lean_ctor_get(v___x_1523_, 1);
lean_inc(v_snd_1524_);
lean_dec_ref(v___x_1523_);
v_out_1525_ = lean_ctor_get(v_snd_1524_, 0);
lean_inc_ref(v_out_1525_);
lean_dec(v_snd_1524_);
return v_out_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object* v_f_1526_, lean_object* v_indent_1527_, lean_object* v_w_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_1526_, v_indent_1527_, v_w_1528_);
lean_dec(v_w_1528_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_nat_to_int(v_a_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object* v_acc_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1534_ = lean_array_get_size(v_a_1533_);
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_nat_dec_eq(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_sub(v___x_1534_, v___x_1538_);
v___x_1540_ = lean_array_get_borrowed(v___x_1537_, v_a_1533_, v___x_1539_);
switch(lean_obj_tag(v___x_1540_))
{
case 0:
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v___x_1539_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v___x_1542_ = lean_string_append(v_acc_1532_, v_a_1541_);
v___x_1543_ = lean_array_pop(v_a_1533_);
v_acc_1532_ = v___x_1542_;
v_a_1533_ = v___x_1543_;
goto _start;
}
case 1:
{
lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v___x_1539_);
v_a_1545_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref(v_a_1545_);
v___x_1546_ = lean_array_pop(v_a_1533_);
v___x_1547_ = l_Array_reverse___redArg(v_a_1545_);
v___x_1548_ = l_Array_append___redArg(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v_a_1533_ = v___x_1548_;
goto _start;
}
default: 
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1540_, 1);
lean_inc_ref(v_a_1550_);
v___x_1551_ = lean_array_set(v_a_1533_, v___x_1539_, v_a_1550_);
lean_dec(v___x_1539_);
v_a_1533_ = v___x_1551_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_1533_);
return v_acc_1532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object* v_00_u03b1_1553_, lean_object* v_acc_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v_acc_1554_, v_a_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object* v_tt_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1558_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_mk_empty_array_with_capacity(v___x_1559_);
v___x_1561_ = lean_array_push(v___x_1560_, v_tt_1557_);
v___x_1562_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v___x_1558_, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object* v_00_u03b1_1563_, lean_object* v_tt_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1564_);
return v___x_1565_;
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

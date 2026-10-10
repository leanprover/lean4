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
lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__1));
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_Widget_instInhabitedTaggedText_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_64_;
v_res_64_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object* v_00_u03b1_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_69_;
}
}
lean_object* l_Lean_Widget_instInhabitedTaggedText___redArg(){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_Widget_instInhabitedTaggedText___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_72_;
v_res_72_ = l_Lean_Widget_instInhabitedTaggedText___redArg();
stack->m_obj
 = v_res_72_;
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
uint8_t l_Lean_Widget_instBEqTaggedText_beq___redArg(lean_object* v_inst_82_, lean_object* v_x_83_, lean_object* v_x_84_){
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
LEAN_EXPORT void l_Lean_Widget_instBEqTaggedText_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_82_ = stack[0].m_obj;
lean_object* v_x_83_ = stack[1].m_obj;
lean_object* v_x_84_ = stack[2].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_82_, v_x_83_, v_x_84_);
stack->m_num = v_res_106_;
}
uint8_t l_Lean_Widget_instBEqTaggedText_beq(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_108_, v_x_109_, v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT void l_Lean_Widget_instBEqTaggedText_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_108_ = stack[1].m_obj;
lean_object* v_x_109_ = stack[2].m_obj;
lean_object* v_x_110_ = stack[3].m_obj;
uint8_t v_res_112_;
v_res_112_ = l_Lean_Widget_instBEqTaggedText_beq(lean_box(0), v_inst_108_, v_x_109_, v_x_110_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText_beq___boxed(lean_object* v_00_u03b1_113_, lean_object* v_inst_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lean_Widget_instBEqTaggedText_beq(v_00_u03b1_113_, v_inst_114_, v_x_115_, v_x_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText___redArg(lean_object* v_inst_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_120_, 0, lean_box(0));
lean_closure_set(v___x_120_, 1, v_inst_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instBEqTaggedText(lean_object* v_00_u03b1_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_closure((void*)(l_Lean_Widget_instBEqTaggedText_beq___boxed), 4, 2);
lean_closure_set(v___x_123_, 0, lean_box(0));
lean_closure_set(v___x_123_, 1, v_inst_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(2u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_to_int(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(lean_object* v_inst_146_, lean_object* v_x_147_, lean_object* v_prec_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_146_, v_x_147_, v_prec_148_);
lean_dec(v_prec_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___redArg(lean_object* v_inst_150_, lean_object* v_x_151_, lean_object* v_prec_152_){
_start:
{
switch(lean_obj_tag(v_x_151_))
{
case 0:
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_173_; 
lean_dec_ref(v_inst_150_);
v_a_153_ = lean_ctor_get(v_x_151_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_173_ == 0)
{
v___x_155_ = v_x_151_;
v_isShared_156_ = v_isSharedCheck_173_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v_x_151_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_173_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___y_158_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1024u);
v___x_170_ = lean_nat_dec_le(v___x_169_, v_prec_152_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_158_ = v___x_171_;
goto v___jp_157_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_158_ = v___x_172_;
goto v___jp_157_;
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2));
v___x_160_ = l_String_quote(v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 3);
lean_ctor_set(v___x_155_, 0, v___x_160_);
v___x_162_ = v___x_155_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_168_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_159_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
lean_inc(v___y_158_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___y_158_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = l_Repr_addAppParen(v___x_166_, v_prec_152_);
return v___x_167_;
}
}
}
}
case 1:
{
lean_object* v_a_174_; lean_object* v_localinst_175_; lean_object* v___y_177_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_a_174_ = lean_ctor_get(v_x_151_, 0);
lean_inc_ref(v_a_174_);
lean_dec_ref_known(v_x_151_, 1);
v_localinst_175_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_175_, 0, v_inst_150_);
v___x_185_ = lean_unsigned_to_nat(1024u);
v___x_186_ = lean_nat_dec_le(v___x_185_, v_prec_152_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_177_ = v___x_187_;
goto v___jp_176_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_177_ = v___x_188_;
goto v___jp_176_;
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_178_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7));
v___x_179_ = l_Array_repr___redArg(v_localinst_175_, v_a_174_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
lean_inc(v___y_177_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_177_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 0;
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
v___x_184_ = l_Repr_addAppParen(v___x_183_, v_prec_152_);
return v___x_184_;
}
}
default: 
{
lean_object* v_a_189_; lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_213_; 
v_a_189_ = lean_ctor_get(v_x_151_, 0);
v_a_190_ = lean_ctor_get(v_x_151_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_213_ == 0)
{
v___x_192_ = v_x_151_;
v_isShared_193_ = v_isSharedCheck_213_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_inc(v_a_189_);
lean_dec(v_x_151_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_213_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___y_196_; uint8_t v___x_210_; 
v___x_194_ = lean_unsigned_to_nat(1024u);
v___x_210_ = lean_nat_dec_le(v___x_194_, v_prec_152_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3);
v___y_196_ = v___x_211_;
goto v___jp_195_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4, &l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once, _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4);
v___y_196_ = v___x_212_;
goto v___jp_195_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_197_ = lean_box(1);
v___x_198_ = ((lean_object*)(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10));
lean_inc_ref(v_inst_150_);
v___x_199_ = lean_apply_2(v_inst_150_, v_a_189_, v___x_194_);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 5);
lean_ctor_set(v___x_192_, 1, v___x_199_);
lean_ctor_set(v___x_192_, 0, v___x_198_);
v___x_201_ = v___x_192_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_209_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_197_);
v___x_203_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_150_, v_a_190_, v___x_194_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
lean_inc(v___y_196_);
v___x_205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_205_, 0, v___y_196_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = 0;
v___x_207_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*1, v___x_206_);
v___x_208_ = l_Repr_addAppParen(v___x_207_, v_prec_152_);
return v___x_208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_x_216_, lean_object* v_prec_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_215_, v_x_216_, v_prec_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText_repr___boxed(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_x_221_, lean_object* v_prec_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Widget_instReprTaggedText_repr(v_00_u03b1_219_, v_inst_220_, v_x_221_, v_prec_222_);
lean_dec(v_prec_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText___redArg(lean_object* v_inst_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_225_, 0, lean_box(0));
lean_closure_set(v___x_225_, 1, v_inst_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instReprTaggedText(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_alloc_closure((void*)(l_Lean_Widget_instReprTaggedText_repr___boxed), 4, 2);
lean_closure_set(v___x_228_, 0, lean_box(0));
lean_closure_set(v___x_228_, 1, v_inst_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(lean_object* v_inst_238_, lean_object* v_json_239_){
_start:
{
lean_object* v___x_240_; 
lean_inc(v_json_239_);
v___x_240_ = l_Lean_Json_getTag_x3f(v_json_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_dec(v_json_239_);
lean_dec_ref(v_inst_238_);
v___x_241_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1));
return v___x_241_;
}
else
{
lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_359_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_359_ == 0)
{
v___x_244_ = v___x_240_;
v_isShared_245_ = v_isSharedCheck_359_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_dec(v___x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_359_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_248_ = lean_string_dec_eq(v_val_242_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
v___x_250_ = lean_string_dec_eq(v_val_242_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; uint8_t v___x_252_; 
lean_del_object(v___x_244_);
v___x_251_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
v___x_252_ = lean_string_dec_eq(v_val_242_, v___x_251_);
lean_dec(v_val_242_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_json_239_);
lean_dec_ref(v_inst_238_);
v___x_253_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6));
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(2u);
v___x_255_ = lean_box(0);
v___x_256_ = l_Lean_Json_parseCtorFields(v_json_239_, v___x_251_, v___x_254_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_inst_238_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_a_265_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_256_, 1);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_array_get_borrowed(v___x_246_, v_a_265_, v___x_266_);
lean_inc_ref(v_inst_238_);
lean_inc(v___x_267_);
v___x_268_ = lean_apply_1(v_inst_238_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_265_);
lean_dec_ref(v_inst_238_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_a_277_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_268_, 1);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_array_get(v___x_246_, v_a_265_, v___x_278_);
lean_dec(v_a_265_);
v___x_280_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_238_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_dec(v_a_277_);
return v___x_280_;
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_285_, 0, v_a_277_);
lean_ctor_set(v___x_285_, 1, v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_val_242_);
lean_dec_ref(v_inst_238_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_box(0);
v___x_292_ = l_Lean_Json_parseCtorFields(v_json_239_, v___x_249_, v___x_290_, v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_del_object(v___x_244_);
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_a_301_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_292_, 1);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_get(v___x_246_, v_a_301_, v___x_302_);
lean_dec(v_a_301_);
v___x_304_ = l_Lean_Json_getStr_x3f(v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_del_object(v___x_244_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v_a_313_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_323_ == 0)
{
v___x_315_ = v___x_304_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_304_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 0);
lean_ctor_set(v___x_244_, 0, v_a_313_);
v___x_318_ = v___x_244_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_val_242_);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_box(0);
v___x_326_ = l_Lean_Json_parseCtorFields(v_json_239_, v___x_247_, v___x_324_, v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_del_object(v___x_244_);
lean_dec_ref(v_inst_238_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v_localinst_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_335_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_326_, 1);
v_localinst_336_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg), 2, 1);
lean_closure_set(v_localinst_336_, 0, v_inst_238_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_array_get(v___x_246_, v_a_335_, v___x_337_);
lean_dec(v_a_335_);
v___x_339_ = l_Lean_Array_fromJson_x3f___redArg(v_localinst_336_, v___x_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_del_object(v___x_244_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_358_; 
v_a_348_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_358_ == 0)
{
v___x_350_ = v___x_339_;
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_339_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v_a_348_);
v___x_353_ = v___x_244_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_json_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_361_, v_json_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText___redArg(lean_object* v_inst_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_365_, 0, lean_box(0));
lean_closure_set(v___x_365_, 1, v_inst_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_closure((void*)(l_Lean_Widget_instFromJsonTaggedText_fromJson), 3, 2);
lean_closure_set(v___x_368_, 0, lean_box(0));
lean_closure_set(v___x_368_, 1, v_inst_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___redArg(lean_object* v_inst_369_, lean_object* v_x_370_){
_start:
{
switch(lean_obj_tag(v_x_370_))
{
case 0:
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_inst_369_);
v_a_371_ = lean_ctor_get(v_x_370_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_383_ == 0)
{
v___x_373_ = v_x_370_;
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v_x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3));
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 3);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_371_);
v___x_377_ = v_reuseFailAlloc_382_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_375_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_Json_mkObj(v___x_380_);
lean_dec_ref_known(v___x_380_, 2);
return v___x_381_;
}
}
}
case 1:
{
lean_object* v_a_384_; lean_object* v_localinst_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_a_384_ = lean_ctor_get(v_x_370_, 0);
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v_x_370_, 1);
v_localinst_385_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson___redArg), 2, 1);
lean_closure_set(v_localinst_385_, 0, v_inst_369_);
v___x_386_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2));
v___x_387_ = l_Lean_Array_toJson___redArg(v_localinst_385_, v_a_384_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_Json_mkObj(v___x_390_);
lean_dec_ref_known(v___x_390_, 2);
return v___x_391_;
}
default: 
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_411_; 
v_a_392_ = lean_ctor_get(v_x_370_, 0);
v_a_393_ = lean_ctor_get(v_x_370_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_411_ == 0)
{
v___x_395_ = v_x_370_;
v_isShared_396_ = v_isSharedCheck_411_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_inc(v_a_392_);
lean_dec(v_x_370_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_411_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_397_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4));
lean_inc_ref(v_inst_369_);
v___x_398_ = lean_apply_1(v_inst_369_, v_a_392_);
v___x_399_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_369_, v_a_393_);
v___x_400_ = lean_unsigned_to_nat(2u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_array_push(v___x_401_, v___x_398_);
v___x_403_ = lean_array_push(v___x_402_, v___x_399_);
v___x_404_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 0);
lean_ctor_set(v___x_395_, 1, v___x_404_);
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_406_ = v___x_395_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_Json_mkObj(v___x_408_);
lean_dec_ref_known(v___x_408_, 2);
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson(lean_object* v_00_u03b1_412_, lean_object* v_inst_413_, lean_object* v_x_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText___redArg(lean_object* v_inst_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_417_, 0, lean_box(0));
lean_closure_set(v___x_417_, 1, v_inst_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Widget_instToJsonTaggedText_toJson), 3, 2);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, v_inst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText___redArg(lean_object* v_s_u2080_421_, lean_object* v_x_422_){
_start:
{
switch(lean_obj_tag(v_x_422_))
{
case 0:
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
v_a_423_ = lean_ctor_get(v_x_422_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_431_ == 0)
{
v___x_425_ = v_x_422_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v_x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_string_append(v_a_423_, v_s_u2080_421_);
lean_dec_ref(v_s_u2080_421_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
case 1:
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_459_; 
v_a_432_ = lean_ctor_get(v_x_422_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_459_ == 0)
{
v___x_434_ = v_x_422_;
v_isShared_435_ = v_isSharedCheck_459_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v_x_422_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_459_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_436_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
v___x_437_ = lean_array_get_size(v_a_432_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_array_get(v___x_436_, v_a_432_, v___x_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_453_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_453_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_453_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_453_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_string_append(v_a_441_, v_s_u2080_421_);
lean_dec_ref(v_s_u2080_421_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_452_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_array_set(v_a_432_, v___x_439_, v___x_447_);
lean_dec(v___x_439_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_448_);
v___x_450_ = v___x_434_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_455_; 
lean_dec(v___x_440_);
lean_dec(v___x_439_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
lean_ctor_set(v___x_434_, 0, v_s_u2080_421_);
v___x_455_ = v___x_434_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_s_u2080_421_);
v___x_455_ = v_reuseFailAlloc_458_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_array_push(v_a_432_, v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
}
default: 
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_s_u2080_421_);
v___x_461_ = lean_unsigned_to_nat(2u);
v___x_462_ = lean_mk_empty_array_with_capacity(v___x_461_);
v___x_463_ = lean_array_push(v___x_462_, v_x_422_);
v___x_464_ = lean_array_push(v___x_463_, v___x_460_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendText(lean_object* v_00_u03b1_466_, lean_object* v_s_u2080_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_u2080_467_, v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag___redArg(lean_object* v_acc_470_, lean_object* v_t_u2080_471_, lean_object* v_a_u2080_472_){
_start:
{
lean_object* v_a_474_; 
switch(lean_obj_tag(v_acc_470_))
{
case 1:
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
v_a_481_ = lean_ctor_get(v_acc_470_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_acc_470_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v_acc_470_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v_acc_470_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_485_, 0, v_t_u2080_471_);
lean_ctor_set(v___x_485_, 1, v_a_u2080_472_);
v___x_486_ = lean_array_push(v_a_481_, v___x_485_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
case 0:
{
lean_object* v_a_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_a_491_ = lean_ctor_get(v_acc_470_, 0);
v___x_492_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_493_ = lean_string_dec_eq(v_a_491_, v___x_492_);
if (v___x_493_ == 0)
{
v_a_474_ = v_acc_470_;
goto v___jp_473_;
}
else
{
lean_object* v___x_494_; 
lean_dec_ref_known(v_acc_470_, 1);
v___x_494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_494_, 0, v_t_u2080_471_);
lean_ctor_set(v___x_494_, 1, v_a_u2080_472_);
return v___x_494_;
}
}
default: 
{
v_a_474_ = v_acc_470_;
goto v___jp_473_;
}
}
v___jp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v_t_u2080_471_);
lean_ctor_set(v___x_475_, 1, v_a_u2080_472_);
v___x_476_ = lean_unsigned_to_nat(2u);
v___x_477_ = lean_mk_empty_array_with_capacity(v___x_476_);
v___x_478_ = lean_array_push(v___x_477_, v_a_474_);
v___x_479_ = lean_array_push(v___x_478_, v___x_475_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_appendTag(lean_object* v_00_u03b1_495_, lean_object* v_acc_496_, lean_object* v_t_u2080_497_, lean_object* v_a_u2080_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_acc_496_, v_t_u2080_497_, v_a_u2080_498_);
return v___x_499_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(lean_object* v_f_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_bs_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_504_ == 0)
{
lean_dec(v_f_500_);
return v_bs_503_;
}
else
{
lean_object* v_v_505_; lean_object* v___x_506_; lean_object* v_bs_x27_507_; lean_object* v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_v_505_ = lean_array_uget(v_bs_503_, v_i_502_);
v___x_506_ = lean_unsigned_to_nat(0u);
v_bs_x27_507_ = lean_array_uset(v_bs_503_, v_i_502_, v___x_506_);
lean_inc(v_f_500_);
v___x_508_ = l_Lean_Widget_TaggedText_map___redArg(v_f_500_, v_v_505_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_502_, v___x_509_);
v___x_511_ = lean_array_uset(v_bs_x27_507_, v_i_502_, v___x_508_);
v_i_502_ = v___x_510_;
v_bs_503_ = v___x_511_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_500_ = stack[0].m_obj;
size_t v_sz_501_ = stack[1].m_num;
size_t v_i_502_ = stack[2].m_num;
lean_object* v_bs_503_ = stack[3].m_obj;
lean_object* v_res_513_;
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_500_, v_sz_501_, v_i_502_, v_bs_503_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map___redArg(lean_object* v_f_514_, lean_object* v_x_515_){
_start:
{
switch(lean_obj_tag(v_x_515_))
{
case 0:
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_f_514_);
v_a_516_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v_x_515_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v_x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
case 1:
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_534_; 
v_a_524_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_534_ == 0)
{
v___x_526_ = v_x_515_;
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v_x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v_sz_528_ = lean_array_size(v_a_524_);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_514_, v_sz_528_, v___x_529_, v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_530_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
default: 
{
lean_object* v_a_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
v_a_535_ = lean_ctor_get(v_x_515_, 0);
v_a_536_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v_x_515_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_inc(v_a_535_);
lean_dec(v_x_515_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_inc(v_f_514_);
v___x_540_ = lean_apply_1(v_f_514_, v_a_535_);
v___x_541_ = l_Lean_Widget_TaggedText_map___redArg(v_f_514_, v_a_536_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_541_);
lean_ctor_set(v___x_538_, 0, v___x_540_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg___boxed(lean_object* v_f_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_bs_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_546_, v_sz_boxed_550_, v_i_boxed_551_, v_bs_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_map(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_f_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Widget_TaggedText_map___redArg(v_f_555_, v_x_556_);
return v___x_557_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_f_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_bs_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_560_, v_sz_561_, v_i_562_, v_bs_563_);
return v___x_564_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_560_ = stack[2].m_obj;
size_t v_sz_561_ = stack[3].m_num;
size_t v_i_562_ = stack[4].m_num;
lean_object* v_bs_563_ = stack[5].m_obj;
lean_object* v_res_565_;
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(lean_box(0), lean_box(0), v_f_560_, v_sz_561_, v_i_562_, v_bs_563_);
stack->m_obj
 = v_res_565_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_f_568_, lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_bs_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_573_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(v_00_u03b1_566_, v_00_u03b2_567_, v_f_568_, v_sz_boxed_572_, v_i_boxed_573_, v_bs_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__0(lean_object* v_toPure_575_, lean_object* v_____do__lift_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_____do__lift_576_);
v___x_578_ = lean_apply_2(v_toPure_575_, lean_box(0), v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__1(lean_object* v_____do__lift_579_, lean_object* v_toPure_580_, lean_object* v_____do__lift_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v_____do__lift_579_);
lean_ctor_set(v___x_582_, 1, v_____do__lift_581_);
v___x_583_ = lean_apply_2(v_toPure_580_, lean_box(0), v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object* v_inst_584_, lean_object* v_f_585_, lean_object* v_x_586_){
_start:
{
switch(lean_obj_tag(v_x_586_))
{
case 0:
{
lean_object* v_toApplicative_587_; lean_object* v_toPure_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
v_toApplicative_587_ = lean_ctor_get(v_inst_584_, 0);
lean_inc_ref(v_toApplicative_587_);
lean_dec(v_f_585_);
lean_dec_ref(v_inst_584_);
v_toPure_588_ = lean_ctor_get(v_toApplicative_587_, 1);
lean_inc(v_toPure_588_);
lean_dec_ref(v_toApplicative_587_);
v_a_589_ = lean_ctor_get(v_x_586_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v_x_586_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v_x_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_apply_2(v_toPure_588_, lean_box(0), v___x_594_);
return v___x_595_;
}
}
}
case 1:
{
lean_object* v_toApplicative_598_; lean_object* v_toBind_599_; lean_object* v_toPure_600_; lean_object* v_a_601_; lean_object* v___f_602_; lean_object* v___x_603_; size_t v_sz_604_; size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_toApplicative_598_ = lean_ctor_get(v_inst_584_, 0);
v_toBind_599_ = lean_ctor_get(v_inst_584_, 1);
lean_inc(v_toBind_599_);
v_toPure_600_ = lean_ctor_get(v_toApplicative_598_, 1);
v_a_601_ = lean_ctor_get(v_x_586_, 0);
lean_inc_ref(v_a_601_);
lean_dec_ref_known(v_x_586_, 1);
lean_inc(v_toPure_600_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_602_, 0, v_toPure_600_);
lean_inc_ref(v_inst_584_);
v___x_603_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg), 3, 2);
lean_closure_set(v___x_603_, 0, v_inst_584_);
lean_closure_set(v___x_603_, 1, v_f_585_);
v_sz_604_ = lean_array_size(v_a_601_);
v___x_605_ = ((size_t)0ULL);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_584_, v___x_603_, v_sz_604_, v___x_605_, v_a_601_);
v___x_607_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_606_, v___f_602_);
return v___x_607_;
}
default: 
{
lean_object* v_toApplicative_608_; lean_object* v_toBind_609_; lean_object* v_toPure_610_; lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_toApplicative_608_ = lean_ctor_get(v_inst_584_, 0);
v_toBind_609_ = lean_ctor_get(v_inst_584_, 1);
lean_inc_n(v_toBind_609_, 2);
v_toPure_610_ = lean_ctor_get(v_toApplicative_608_, 1);
lean_inc(v_toPure_610_);
v_a_611_ = lean_ctor_get(v_x_586_, 0);
lean_inc(v_a_611_);
v_a_612_ = lean_ctor_get(v_x_586_, 1);
lean_inc_ref(v_a_612_);
lean_dec_ref_known(v_x_586_, 2);
lean_inc(v_f_585_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_613_, 0, v_toPure_610_);
lean_closure_set(v___f_613_, 1, v_inst_584_);
lean_closure_set(v___f_613_, 2, v_f_585_);
lean_closure_set(v___f_613_, 3, v_a_612_);
lean_closure_set(v___f_613_, 4, v_toBind_609_);
v___x_614_ = lean_apply_1(v_f_585_, v_a_611_);
v___x_615_ = lean_apply_4(v_toBind_609_, lean_box(0), lean_box(0), v___x_614_, v___f_613_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___redArg___lam__2(lean_object* v_toPure_616_, lean_object* v_inst_617_, lean_object* v_f_618_, lean_object* v_a_619_, lean_object* v_toBind_620_, lean_object* v_____do__lift_621_){
_start:
{
lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_622_, 0, v_____do__lift_621_);
lean_closure_set(v___f_622_, 1, v_toPure_616_);
v___x_623_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_617_, v_f_618_, v_a_619_);
v___x_624_ = lean_apply_4(v_toBind_620_, lean_box(0), lean_box(0), v___x_623_, v___f_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM(lean_object* v_m_625_, lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_inst_628_, lean_object* v_f_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_628_, v_f_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__1(lean_object* v_inst_632_, lean_object* v_f_633_, lean_object* v_a_634_, lean_object* v_____r_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_632_, v_f_633_, v_a_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg(lean_object* v_inst_637_, lean_object* v_f_638_, lean_object* v_x_639_){
_start:
{
switch(lean_obj_tag(v_x_639_))
{
case 0:
{
lean_object* v_toApplicative_640_; lean_object* v_toPure_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_toApplicative_640_ = lean_ctor_get(v_inst_637_, 0);
lean_inc_ref(v_toApplicative_640_);
lean_dec_ref_known(v_x_639_, 1);
lean_dec(v_f_638_);
lean_dec_ref(v_inst_637_);
v_toPure_641_ = lean_ctor_get(v_toApplicative_640_, 1);
lean_inc(v_toPure_641_);
lean_dec_ref(v_toApplicative_640_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_apply_2(v_toPure_641_, lean_box(0), v___x_642_);
return v___x_643_;
}
case 1:
{
lean_object* v_toApplicative_644_; lean_object* v_toPure_645_; lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_toApplicative_644_ = lean_ctor_get(v_inst_637_, 0);
v_toPure_645_ = lean_ctor_get(v_toApplicative_644_, 1);
v_a_646_ = lean_ctor_get(v_x_639_, 0);
lean_inc_ref(v_a_646_);
lean_dec_ref_known(v_x_639_, 1);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_array_get_size(v_a_646_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_inc(v_toPure_645_);
lean_dec_ref(v_a_646_);
lean_dec(v_f_638_);
lean_dec_ref(v_inst_637_);
v___x_651_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_649_);
return v___x_651_;
}
else
{
lean_object* v___f_652_; uint8_t v___x_653_; 
lean_inc_ref(v_inst_637_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_652_, 0, v_inst_637_);
lean_closure_set(v___f_652_, 1, v_f_638_);
v___x_653_ = lean_nat_dec_le(v___x_648_, v___x_648_);
if (v___x_653_ == 0)
{
if (v___x_650_ == 0)
{
lean_object* v___x_654_; 
lean_inc(v_toPure_645_);
lean_dec_ref(v___f_652_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_inst_637_);
v___x_654_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_649_);
return v___x_654_;
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_648_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_637_, v___f_652_, v_a_646_, v___x_655_, v___x_656_, v___x_649_);
return v___x_657_;
}
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_648_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_637_, v___f_652_, v_a_646_, v___x_658_, v___x_659_, v___x_649_);
return v___x_660_;
}
}
}
default: 
{
lean_object* v_toBind_661_; lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_toBind_661_ = lean_ctor_get(v_inst_637_, 1);
lean_inc(v_toBind_661_);
v_a_662_ = lean_ctor_get(v_x_639_, 0);
lean_inc(v_a_662_);
v_a_663_ = lean_ctor_get(v_x_639_, 1);
lean_inc_ref_n(v_a_663_, 2);
lean_dec_ref_known(v_x_639_, 2);
lean_inc(v_f_638_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_forM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_664_, 0, v_inst_637_);
lean_closure_set(v___f_664_, 1, v_f_638_);
lean_closure_set(v___f_664_, 2, v_a_663_);
v___x_665_ = lean_apply_2(v_f_638_, v_a_662_, v_a_663_);
v___x_666_ = lean_apply_4(v_toBind_661_, lean_box(0), lean_box(0), v___x_665_, v___f_664_);
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM___redArg___lam__0(lean_object* v_inst_667_, lean_object* v_f_668_, lean_object* v_x_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_667_, v_f_668_, v___y_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_forM(lean_object* v_m_672_, lean_object* v_00_u03b1_673_, lean_object* v_inst_674_, lean_object* v_f_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_674_, v_f_675_, v_x_676_);
return v___x_677_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(lean_object* v_f_678_, size_t v_sz_679_, size_t v_i_680_, lean_object* v_bs_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_682_ == 0)
{
lean_dec_ref(v_f_678_);
return v_bs_681_;
}
else
{
lean_object* v_v_683_; lean_object* v___x_684_; lean_object* v_bs_x27_685_; lean_object* v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v_v_683_ = lean_array_uget(v_bs_681_, v_i_680_);
v___x_684_ = lean_unsigned_to_nat(0u);
v_bs_x27_685_ = lean_array_uset(v_bs_681_, v_i_680_, v___x_684_);
lean_inc_ref(v_f_678_);
v___x_686_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_678_, v_v_683_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_i_680_, v___x_687_);
v___x_689_ = lean_array_uset(v_bs_x27_685_, v_i_680_, v___x_686_);
v_i_680_ = v___x_688_;
v_bs_681_ = v___x_689_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_678_ = stack[0].m_obj;
size_t v_sz_679_ = stack[1].m_num;
size_t v_i_680_ = stack[2].m_num;
lean_object* v_bs_681_ = stack[3].m_obj;
lean_object* v_res_691_;
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_678_, v_sz_679_, v_i_680_, v_bs_681_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object* v_f_692_, lean_object* v_x_693_){
_start:
{
switch(lean_obj_tag(v_x_693_))
{
case 0:
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_f_692_);
v_a_694_ = lean_ctor_get(v_x_693_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_693_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v_x_693_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v_x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
case 1:
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_712_; 
v_a_702_ = lean_ctor_get(v_x_693_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_693_);
if (v_isSharedCheck_712_ == 0)
{
v___x_704_ = v_x_693_;
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v_x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
size_t v_sz_706_; size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v_sz_706_ = lean_array_size(v_a_702_);
v___x_707_ = ((size_t)0ULL);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_692_, v_sz_706_, v___x_707_, v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_708_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
default: 
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_713_ = lean_ctor_get(v_x_693_, 0);
lean_inc(v_a_713_);
v_a_714_ = lean_ctor_get(v_x_693_, 1);
lean_inc_ref(v_a_714_);
lean_dec_ref_known(v_x_693_, 2);
v___x_715_ = lean_apply_2(v_f_692_, v_a_713_, v_a_714_);
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg___boxed(lean_object* v_f_716_, lean_object* v_sz_717_, lean_object* v_i_718_, lean_object* v_bs_719_){
_start:
{
size_t v_sz_boxed_720_; size_t v_i_boxed_721_; lean_object* v_res_722_; 
v_sz_boxed_720_ = lean_unbox_usize(v_sz_717_);
lean_dec(v_sz_717_);
v_i_boxed_721_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_716_, v_sz_boxed_720_, v_i_boxed_721_, v_bs_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewrite(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_f_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_725_, v_x_726_);
return v___x_727_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_f_730_, size_t v_sz_731_, size_t v_i_732_, lean_object* v_bs_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_730_, v_sz_731_, v_i_732_, v_bs_733_);
return v___x_734_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_730_ = stack[2].m_obj;
size_t v_sz_731_ = stack[3].m_num;
size_t v_i_732_ = stack[4].m_num;
lean_object* v_bs_733_ = stack[5].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(lean_box(0), lean_box(0), v_f_730_, v_sz_731_, v_i_732_, v_bs_733_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_f_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_bs_741_){
_start:
{
size_t v_sz_boxed_742_; size_t v_i_boxed_743_; lean_object* v_res_744_; 
v_sz_boxed_742_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_743_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(v_00_u03b1_736_, v_00_u03b2_737_, v_f_738_, v_sz_boxed_742_, v_i_boxed_743_, v_bs_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___redArg(lean_object* v_inst_745_, lean_object* v_f_746_, lean_object* v_x_747_){
_start:
{
switch(lean_obj_tag(v_x_747_))
{
case 0:
{
lean_object* v_toApplicative_748_; lean_object* v_toPure_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_toApplicative_748_ = lean_ctor_get(v_inst_745_, 0);
lean_inc_ref(v_toApplicative_748_);
lean_dec(v_f_746_);
lean_dec_ref(v_inst_745_);
v_toPure_749_ = lean_ctor_get(v_toApplicative_748_, 1);
lean_inc(v_toPure_749_);
lean_dec_ref(v_toApplicative_748_);
v_a_750_ = lean_ctor_get(v_x_747_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v_x_747_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v_x_747_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_757_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = lean_apply_2(v_toPure_749_, lean_box(0), v___x_755_);
return v___x_756_;
}
}
}
case 1:
{
lean_object* v_toApplicative_759_; lean_object* v_toBind_760_; lean_object* v_toPure_761_; lean_object* v_a_762_; lean_object* v___f_763_; lean_object* v___x_764_; size_t v_sz_765_; size_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_toApplicative_759_ = lean_ctor_get(v_inst_745_, 0);
v_toBind_760_ = lean_ctor_get(v_inst_745_, 1);
lean_inc(v_toBind_760_);
v_toPure_761_ = lean_ctor_get(v_toApplicative_759_, 1);
v_a_762_ = lean_ctor_get(v_x_747_, 0);
lean_inc_ref(v_a_762_);
lean_dec_ref_known(v_x_747_, 1);
lean_inc(v_toPure_761_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_763_, 0, v_toPure_761_);
lean_inc_ref(v_inst_745_);
v___x_764_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_rewriteM___redArg), 3, 2);
lean_closure_set(v___x_764_, 0, v_inst_745_);
lean_closure_set(v___x_764_, 1, v_f_746_);
v_sz_765_ = lean_array_size(v_a_762_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_745_, v___x_764_, v_sz_765_, v___x_766_, v_a_762_);
v___x_768_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_767_, v___f_763_);
return v___x_768_;
}
default: 
{
lean_object* v_a_769_; lean_object* v_a_770_; lean_object* v___x_771_; 
lean_dec_ref(v_inst_745_);
v_a_769_ = lean_ctor_get(v_x_747_, 0);
lean_inc(v_a_769_);
v_a_770_ = lean_ctor_get(v_x_747_, 1);
lean_inc_ref(v_a_770_);
lean_dec_ref_known(v_x_747_, 2);
v___x_771_ = lean_apply_2(v_f_746_, v_a_769_, v_a_770_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM(lean_object* v_m_772_, lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_inst_775_, lean_object* v_f_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Widget_TaggedText_rewriteM___redArg(v_inst_775_, v_f_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(lean_object* v_inst_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v_a_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_rpcEncode_784_; lean_object* v___x_648__overap_785_; lean_object* v___x_786_; lean_object* v_fst_787_; lean_object* v_snd_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_rpcEncode_784_ = lean_ctor_get(v_inst_779_, 0);
lean_inc_ref(v_rpcEncode_784_);
lean_dec_ref(v_inst_779_);
v___x_648__overap_785_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_780_, v_rpcEncode_784_, v_a_782_);
v___x_786_ = lean_apply_1(v___x_648__overap_785_, v___y_783_);
v_fst_787_ = lean_ctor_get(v___x_786_, 0);
v_snd_788_ = lean_ctor_get(v___x_786_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_786_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snd_788_);
lean_inc(v_fst_787_);
lean_dec(v___x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v___x_781_, v_fst_787_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_788_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(lean_object* v___f_797_, lean_object* v_inst_798_, lean_object* v___x_799_, lean_object* v_a_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v___f_797_, v_a_800_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v___x_799_);
lean_dec_ref(v_inst_798_);
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v_rpcDecode_812_; lean_object* v___x_661__overap_813_; lean_object* v___x_814_; 
v_a_811_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_802_, 1);
v_rpcDecode_812_ = lean_ctor_get(v_inst_798_, 1);
lean_inc_ref(v_rpcDecode_812_);
lean_dec_ref(v_inst_798_);
v___x_661__overap_813_ = l_Lean_Widget_TaggedText_mapM___redArg(v___x_799_, v_rpcDecode_812_, v_a_811_);
lean_inc_ref(v___y_801_);
v___x_814_ = lean_apply_1(v___x_661__overap_813_, v___y_801_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed(lean_object* v___f_815_, lean_object* v_inst_816_, lean_object* v___x_817_, lean_object* v_a_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(v___f_815_, v_inst_816_, v___x_817_, v_a_818_, v___y_819_);
lean_dec_ref(v___y_819_);
return v_res_820_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9));
v___x_868_ = l_ReaderT_instMonad___redArg(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22(void){
_start:
{
lean_object* v___x_869_; lean_object* v___f_870_; 
v___x_869_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_870_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_870_, 0, v___x_869_);
return v___f_870_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23(void){
_start:
{
lean_object* v___x_871_; lean_object* v___f_872_; 
v___x_871_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_872_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_872_, 0, v___x_871_);
return v___f_872_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24(void){
_start:
{
lean_object* v___x_873_; lean_object* v___f_874_; 
v___x_873_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_874_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_874_, 0, v___x_873_);
return v___f_874_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25(void){
_start:
{
lean_object* v___x_875_; lean_object* v___f_876_; 
v___x_875_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___f_876_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_876_, 0, v___x_875_);
return v___f_876_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_878_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_878_, 0, lean_box(0));
lean_closure_set(v___x_878_, 1, lean_box(0));
lean_closure_set(v___x_878_, 2, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27(void){
_start:
{
lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___f_879_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22);
v___x_880_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___f_879_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_883_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_883_, 0, lean_box(0));
lean_closure_set(v___x_883_, 1, lean_box(0));
lean_closure_set(v___x_883_, 2, v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29(void){
_start:
{
lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___f_884_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25);
v___f_885_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24);
v___f_886_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23);
v___x_887_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28);
v___x_888_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27);
v___x_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___f_886_);
lean_ctor_set(v___x_889_, 3, v___f_885_);
lean_ctor_set(v___x_889_, 4, v___f_884_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21);
v___x_891_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_891_, 0, lean_box(0));
lean_closure_set(v___x_891_, 1, lean_box(0));
lean_closure_set(v___x_891_, 2, v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30);
v___x_893_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable___redArg(lean_object* v_inst_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___x_903_; 
v___x_897_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_898_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20));
lean_inc_ref(v_inst_896_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0), 5, 3);
lean_closure_set(v___f_899_, 0, v_inst_896_);
lean_closure_set(v___f_899_, 1, v___x_897_);
lean_closure_set(v___f_899_, 2, v___x_898_);
v___x_900_ = lean_obj_once(&l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31, &l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once, _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31);
v___f_901_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32));
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_902_, 0, v___f_901_);
lean_closure_set(v___f_902_, 1, v_inst_896_);
lean_closure_set(v___f_902_, 2, v___x_900_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___f_899_);
lean_ctor_set(v___x_903_, 1, v___f_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_instRpcEncodable(lean_object* v_00_u03b1_904_, lean_object* v_inst_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(lean_object* v_s_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_out_917_; lean_object* v_tagStack_918_; lean_object* v_column_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_931_; 
v_out_917_ = lean_ctor_get(v___y_916_, 0);
v_tagStack_918_ = lean_ctor_get(v___y_916_, 1);
v_column_919_ = lean_ctor_get(v___y_916_, 2);
v_isSharedCheck_931_ = !lean_is_exclusive(v___y_916_);
if (v_isSharedCheck_931_ == 0)
{
v___x_921_ = v___y_916_;
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_column_919_);
lean_inc(v_tagStack_918_);
lean_inc(v_out_917_);
lean_dec(v___y_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_923_ = lean_box(0);
lean_inc_ref(v_s_915_);
v___x_924_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_915_, v_out_917_);
v___x_925_ = lean_string_length(v_s_915_);
lean_dec_ref(v_s_915_);
v___x_926_ = lean_nat_add(v_column_919_, v___x_925_);
lean_dec(v_column_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v___x_926_);
lean_ctor_set(v___x_921_, 0, v___x_924_);
v___x_928_ = v___x_921_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_tagStack_918_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v___x_926_);
v___x_928_ = v_reuseFailAlloc_930_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_923_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
return v___x_929_;
}
}
}
}
lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(uint32_t v___x_932_, lean_object* v_s_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_string_push(v_s_933_, v___x_932_);
return v___x_934_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_932_ = stack[0].m_num;
lean_object* v_s_933_ = stack[1].m_obj;
lean_object* v_res_935_;
v_res_935_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_932_, v_s_933_);
stack->m_obj
 = v_res_935_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(lean_object* v___x_936_, lean_object* v_s_937_){
_start:
{
uint32_t v___x_850__boxed_938_; lean_object* v_res_939_; 
v___x_850__boxed_938_ = lean_unbox_uint32(v___x_936_);
lean_dec(v___x_936_);
v_res_939_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_850__boxed_938_, v_s_937_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_941_; lean_object* v___x_942_; 
v___x_941_ = 32;
v___x_942_ = lean_box_uint32(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___f_944_; 
v___x_943_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
v___f_944_ = lean_alloc_closure((void*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed), 2, 1);
lean_closure_set(v___f_944_, 0, v___x_943_);
return v___f_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(lean_object* v_indent_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_out_947_; lean_object* v_tagStack_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_961_; 
v_out_947_ = lean_ctor_get(v___y_946_, 0);
v_tagStack_948_ = lean_ctor_get(v___y_946_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v___y_946_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___y_946_, 2);
lean_dec(v_unused_962_);
v___x_950_ = v___y_946_;
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_tagStack_948_);
lean_inc(v_out_947_);
lean_dec(v___y_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_952_ = lean_box(0);
v___x_953_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
v___f_954_ = lean_obj_once(&l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1, &l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once, _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
lean_inc(v_indent_945_);
v___x_955_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_954_, v_indent_945_, v___x_953_);
v___x_956_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_955_, v_out_947_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 2, v_indent_945_);
lean_ctor_set(v___x_950_, 0, v___x_956_);
v___x_958_ = v___x_950_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_tagStack_948_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_indent_945_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_952_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(lean_object* v_____do__lift_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_column_965_; lean_object* v___x_966_; 
v_column_965_ = lean_ctor_get(v_____do__lift_963_, 2);
lean_inc(v_column_965_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_column_965_);
lean_ctor_set(v___x_966_, 1, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(lean_object* v_____do__lift_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_967_, v___y_968_);
lean_dec_ref(v_____do__lift_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(lean_object* v_n_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_out_972_; lean_object* v_tagStack_973_; lean_object* v_column_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v_out_972_ = lean_ctor_get(v___y_971_, 0);
v_tagStack_973_ = lean_ctor_get(v___y_971_, 1);
v_column_974_ = lean_ctor_get(v___y_971_, 2);
v_isSharedCheck_987_ = !lean_is_exclusive(v___y_971_);
if (v_isSharedCheck_987_ == 0)
{
v___x_976_ = v___y_971_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_column_974_);
lean_inc(v_tagStack_973_);
lean_inc(v_out_972_);
lean_dec(v___y_971_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_978_ = lean_box(0);
v___x_979_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_974_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_column_974_);
lean_ctor_set(v___x_980_, 1, v_out_972_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_n_970_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_tagStack_973_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_982_);
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_984_ = v___x_976_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_column_974_);
v___x_984_ = v_reuseFailAlloc_986_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_978_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(lean_object* v_acc_988_, lean_object* v_x_989_){
_start:
{
lean_object* v_snd_990_; lean_object* v_fst_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1001_; 
v_snd_990_ = lean_ctor_get(v_x_989_, 1);
lean_inc(v_snd_990_);
v_fst_991_ = lean_ctor_get(v_x_989_, 0);
lean_inc(v_fst_991_);
lean_dec_ref(v_x_989_);
v_fst_992_ = lean_ctor_get(v_snd_990_, 0);
v_snd_993_ = lean_ctor_get(v_snd_990_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_snd_990_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_995_ = v_snd_990_;
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v_snd_990_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v_fst_992_);
lean_ctor_set(v___x_995_, 0, v_fst_991_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_fst_991_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_fst_992_);
v___x_998_ = v_reuseFailAlloc_1000_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_993_, v___x_998_, v_acc_988_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(lean_object* v___f_1004_, lean_object* v_n_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_out_1007_; lean_object* v_tagStack_1008_; lean_object* v_column_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1022_; 
v_out_1007_ = lean_ctor_get(v___y_1006_, 0);
v_tagStack_1008_ = lean_ctor_get(v___y_1006_, 1);
v_column_1009_ = lean_ctor_get(v___y_1006_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___y_1006_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1011_ = v___y_1006_;
v_isShared_1012_ = v_isSharedCheck_1022_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_column_1009_);
lean_inc(v_tagStack_1008_);
lean_inc(v_out_1007_);
lean_dec(v___y_1006_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1022_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_out_x27_1017_; lean_object* v___x_1019_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_n_1005_);
lean_inc(v_tagStack_1008_);
v___x_1015_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1008_, v_tagStack_1008_, v_n_1005_, v___x_1014_);
v___x_1016_ = l_List_drop___redArg(v_n_1005_, v_tagStack_1008_);
lean_dec(v_tagStack_1008_);
v_out_x27_1017_ = l_List_foldl___redArg(v___f_1004_, v_out_1007_, v___x_1015_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1016_);
lean_ctor_set(v___x_1011_, 0, v_out_x27_1017_);
v___x_1019_ = v___x_1011_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_out_x27_1017_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_column_1009_);
v___x_1019_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1013_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_zero_1045_; uint8_t v_isZero_1046_; 
v_zero_1045_ = lean_unsigned_to_nat(0u);
v_isZero_1046_ = lean_nat_dec_eq(v_x_1043_, v_zero_1045_);
if (v_isZero_1046_ == 1)
{
lean_dec(v_x_1043_);
return v_x_1044_;
}
else
{
uint32_t v___x_1047_; lean_object* v_one_1048_; lean_object* v_n_1049_; lean_object* v___x_1050_; 
v___x_1047_ = 32;
v_one_1048_ = lean_unsigned_to_nat(1u);
v_n_1049_ = lean_nat_sub(v_x_1043_, v_one_1048_);
lean_dec(v_x_1043_);
v___x_1050_ = lean_string_push(v_x_1044_, v___x_1047_);
v_x_1043_ = v_n_1049_;
v_x_1044_ = v___x_1050_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(lean_object* v_fla_1052_, uint8_t v_flb_1053_, lean_object* v_tail_1054_, lean_object* v_is_x27_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1056_, 0, v_fla_1052_);
lean_ctor_set(v___x_1056_, 1, v_is_x27_1055_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*2, v_flb_1053_);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_tail_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fla_1052_ = stack[0].m_obj;
uint8_t v_flb_1053_ = stack[1].m_num;
lean_object* v_tail_1054_ = stack[2].m_obj;
lean_object* v_is_x27_1055_ = stack[3].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1052_, v_flb_1053_, v_tail_1054_, v_is_x27_1055_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(lean_object* v_fla_1059_, lean_object* v_flb_1060_, lean_object* v_tail_1061_, lean_object* v_is_x27_1062_){
_start:
{
uint8_t v_flb_6286__boxed_1063_; lean_object* v_res_1064_; 
v_flb_6286__boxed_1063_ = lean_unbox(v_flb_1060_);
v_res_1064_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1059_, v_flb_6286__boxed_1063_, v_tail_1061_, v_is_x27_1062_);
return v_res_1064_;
}
}
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(uint8_t v_flb_1065_, lean_object* v_items_1066_, lean_object* v_gs_1067_, lean_object* v_w_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___y_1071_; lean_object* v_column_1076_; uint8_t v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v_g_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_r_1084_; lean_object* v___y_1086_; uint8_t v_foundLine_1091_; lean_object* v_space_1092_; uint8_t v___x_1093_; 
v_column_1076_ = lean_ctor_get(v___y_1069_, 2);
v___x_1077_ = 0;
v___x_1078_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1065_, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1079_, 0, v___x_1078_);
lean_inc(v_items_1066_);
v_g_1080_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1080_, 0, v___x_1079_);
lean_ctor_set(v_g_1080_, 1, v_items_1066_);
lean_ctor_set_uint8(v_g_1080_, sizeof(void*)*2, v_flb_1065_);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_g_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_nat_sub(v_w_1068_, v_column_1076_);
lean_inc(v___x_1083_);
lean_inc(v_column_1076_);
v_r_1084_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1082_, v_column_1076_, v___x_1083_);
v_foundLine_1091_ = lean_ctor_get_uint8(v_r_1084_, sizeof(void*)*1);
v_space_1092_ = lean_ctor_get(v_r_1084_, 0);
v___x_1093_ = lean_nat_dec_lt(v___x_1083_, v_space_1092_);
if (v___x_1093_ == 0)
{
if (v_foundLine_1091_ == 0)
{
lean_object* v___x_1094_; lean_object* v_r_u2082_1095_; uint8_t v_foundLine_1096_; uint8_t v_foundFlattenedHardLine_1097_; lean_object* v_space_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1106_; 
v___x_1094_ = lean_nat_sub(v___x_1083_, v_space_1092_);
lean_inc(v_column_1076_);
lean_inc(v_gs_1067_);
v_r_u2082_1095_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1067_, v_column_1076_, v___x_1094_);
v_foundLine_1096_ = lean_ctor_get_uint8(v_r_u2082_1095_, sizeof(void*)*1);
v_foundFlattenedHardLine_1097_ = lean_ctor_get_uint8(v_r_u2082_1095_, sizeof(void*)*1 + 1);
v_space_1098_ = lean_ctor_get(v_r_u2082_1095_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_r_u2082_1095_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1100_ = v_r_u2082_1095_;
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_space_1098_);
lean_dec(v_r_u2082_1095_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_nat_add(v_space_1092_, v_space_1098_);
lean_dec(v_space_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*1, v_foundLine_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1097_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v___y_1086_ = v___x_1104_;
goto v___jp_1085_;
}
}
}
else
{
lean_inc_ref(v_r_1084_);
v___y_1086_ = v_r_1084_;
goto v___jp_1085_;
}
}
else
{
lean_inc_ref(v_r_1084_);
v___y_1086_ = v_r_1084_;
goto v___jp_1085_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1072_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1072_, 0, v___y_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_items_1066_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*2, v_flb_1065_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_gs_1067_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___y_1069_);
return v___x_1075_;
}
v___jp_1085_:
{
uint8_t v_foundFlattenedHardLine_1087_; 
v_foundFlattenedHardLine_1087_ = lean_ctor_get_uint8(v_r_1084_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1084_);
if (v_foundFlattenedHardLine_1087_ == 0)
{
lean_object* v_space_1088_; uint8_t v___x_1089_; 
v_space_1088_ = lean_ctor_get(v___y_1086_, 0);
lean_inc(v_space_1088_);
lean_dec_ref(v___y_1086_);
v___x_1089_ = lean_nat_dec_le(v_space_1088_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v_space_1088_);
v___y_1071_ = v___x_1089_;
goto v___jp_1070_;
}
else
{
uint8_t v___x_1090_; 
lean_dec_ref(v___y_1086_);
lean_dec(v___x_1083_);
v___x_1090_ = 0;
v___y_1071_ = v___x_1090_;
goto v___jp_1070_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_flb_1065_ = stack[0].m_num;
lean_object* v_items_1066_ = stack[1].m_obj;
lean_object* v_gs_1067_ = stack[2].m_obj;
lean_object* v_w_1068_ = stack[3].m_obj;
lean_object* v___y_1069_ = stack[4].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1065_, v_items_1066_, v_gs_1067_, v_w_1068_, v___y_1069_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(lean_object* v_flb_1108_, lean_object* v_items_1109_, lean_object* v_gs_1110_, lean_object* v_w_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v_flb_boxed_1113_; lean_object* v_res_1114_; 
v_flb_boxed_1113_ = lean_unbox(v_flb_1108_);
v_res_1114_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_1113_, v_items_1109_, v_gs_1110_, v_w_1111_, v___y_1112_);
lean_dec(v_w_1111_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
return v_x_1115_;
}
else
{
lean_object* v_head_1117_; lean_object* v_snd_1118_; lean_object* v_tail_1119_; lean_object* v_fst_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1131_; 
v_head_1117_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_head_1117_);
v_snd_1118_ = lean_ctor_get(v_head_1117_, 1);
lean_inc(v_snd_1118_);
v_tail_1119_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_tail_1119_);
lean_dec_ref_known(v_x_1116_, 2);
v_fst_1120_ = lean_ctor_get(v_head_1117_, 0);
lean_inc(v_fst_1120_);
lean_dec(v_head_1117_);
v_fst_1121_ = lean_ctor_get(v_snd_1118_, 0);
v_snd_1122_ = lean_ctor_get(v_snd_1118_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_snd_1118_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1124_ = v_snd_1118_;
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snd_1122_);
lean_inc(v_fst_1121_);
lean_dec(v_snd_1118_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v_fst_1121_);
lean_ctor_set(v___x_1124_, 0, v_fst_1120_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_fst_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_fst_1121_);
v___x_1127_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Widget_TaggedText_appendTag___redArg(v_snd_1122_, v___x_1127_, v_x_1115_);
v_x_1115_ = v___x_1128_;
v_x_1116_ = v_tail_1119_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_box(0);
v___x_1133_ = ((lean_object*)(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19));
v___x_1134_ = l_instInhabitedOfMonad___redArg(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(lean_object* v_msg_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_6185__overap_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_obj_once(&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0, &l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once, _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
v___x_6185__overap_1138_ = lean_panic_fn_borrowed(v___x_1137_, v_msg_1135_);
v___x_1139_ = lean_apply_1(v___x_6185__overap_1138_, v___y_1136_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1142_ = lean_string_length(v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(lean_object* v_w_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___y_1146_);
return v___x_1148_;
}
else
{
lean_object* v_head_1149_; lean_object* v_items_1150_; 
v_head_1149_ = lean_ctor_get(v_x_1145_, 0);
v_items_1150_ = lean_ctor_get(v_head_1149_, 1);
lean_inc(v_items_1150_);
if (lean_obj_tag(v_items_1150_) == 0)
{
lean_object* v_tail_1151_; 
v_tail_1151_ = lean_ctor_get(v_x_1145_, 1);
lean_inc(v_tail_1151_);
lean_dec_ref_known(v_x_1145_, 2);
v_x_1145_ = v_tail_1151_;
goto _start;
}
else
{
lean_object* v_head_1153_; lean_object* v_tail_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1505_; 
lean_inc(v_head_1149_);
v_head_1153_ = lean_ctor_get(v_items_1150_, 0);
lean_inc(v_head_1153_);
v_tail_1154_ = lean_ctor_get(v_x_1145_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_x_1145_, 0);
lean_dec(v_unused_1506_);
v___x_1156_ = v_x_1145_;
v_isShared_1157_ = v_isSharedCheck_1505_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_tail_1154_);
lean_dec(v_x_1145_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1505_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_fla_1158_; uint8_t v_flb_1159_; lean_object* v_tail_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1503_; 
v_fla_1158_ = lean_ctor_get(v_head_1149_, 0);
lean_inc(v_fla_1158_);
v_flb_1159_ = lean_ctor_get_uint8(v_head_1149_, sizeof(void*)*2);
lean_dec(v_head_1149_);
v_tail_1160_ = lean_ctor_get(v_items_1150_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_items_1150_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_items_1150_, 0);
lean_dec(v_unused_1504_);
v___x_1162_ = v_items_1150_;
v_isShared_1163_ = v_isSharedCheck_1503_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_tail_1160_);
lean_dec(v_items_1150_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1503_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_f_1164_; lean_object* v_indent_1165_; lean_object* v_activeTags_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1502_; 
v_f_1164_ = lean_ctor_get(v_head_1153_, 0);
v_indent_1165_ = lean_ctor_get(v_head_1153_, 1);
v_activeTags_1166_ = lean_ctor_get(v_head_1153_, 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_head_1153_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1168_ = v_head_1153_;
v_isShared_1169_ = v_isSharedCheck_1502_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_activeTags_1166_);
lean_inc(v_indent_1165_);
lean_inc(v_f_1164_);
lean_dec(v_head_1153_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1502_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint8_t v___y_1211_; 
switch(lean_obj_tag(v_f_1164_))
{
case 0:
{
lean_object* v_out_1228_; lean_object* v_tagStack_1229_; lean_object* v_column_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1243_; 
lean_del_object(v___x_1168_);
lean_dec(v_indent_1165_);
lean_del_object(v___x_1162_);
lean_del_object(v___x_1156_);
v_out_1228_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1229_ = lean_ctor_get(v___y_1146_, 1);
v_column_1230_ = lean_ctor_get(v___y_1146_, 2);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1232_ = v___y_1146_;
v_isShared_1233_ = v_isSharedCheck_1243_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_column_1230_);
lean_inc(v_tagStack_1229_);
lean_inc(v_out_1228_);
lean_dec(v___y_1146_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1243_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_out_x27_1237_; lean_object* v___x_1239_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1229_);
v___x_1235_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1229_, v_tagStack_1229_, v_activeTags_1166_, v___x_1234_);
v___x_1236_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1229_);
lean_dec(v_tagStack_1229_);
v_out_x27_1237_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1228_, v___x_1235_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1236_);
lean_ctor_set(v___x_1232_, 0, v_out_x27_1237_);
v___x_1239_ = v___x_1232_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_out_x27_1237_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_column_1230_);
v___x_1239_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1240_;
v___y_1146_ = v___x_1239_;
goto _start;
}
}
}
case 1:
{
lean_del_object(v___x_1168_);
lean_del_object(v___x_1162_);
lean_del_object(v___x_1156_);
if (v_flb_1159_ == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1158_);
if (v___x_1244_ == 0)
{
lean_object* v_out_1245_; lean_object* v_tagStack_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1263_; 
v_out_1245_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1246_ = lean_ctor_get(v___y_1146_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___y_1146_, 2);
lean_dec(v_unused_1264_);
v___x_1248_ = v___y_1146_;
v_isShared_1249_ = v_isSharedCheck_1263_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_tagStack_1246_);
lean_inc(v_out_1245_);
lean_dec(v___y_1146_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1263_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_out_x27_1257_; lean_object* v___x_1259_; 
v___x_1250_ = l_Int_toNat(v_indent_1165_);
lean_dec(v_indent_1165_);
v___x_1251_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1250_);
v___x_1252_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1250_, v___x_1251_);
v___x_1253_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1252_, v_out_1245_);
v___x_1254_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1246_);
v___x_1255_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1246_, v_tagStack_1246_, v_activeTags_1166_, v___x_1254_);
v___x_1256_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1246_);
lean_dec(v_tagStack_1246_);
v_out_x27_1257_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1253_, v___x_1255_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 2, v___x_1250_);
lean_ctor_set(v___x_1248_, 1, v___x_1256_);
lean_ctor_set(v___x_1248_, 0, v_out_x27_1257_);
v___x_1259_ = v___x_1248_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_out_x27_1257_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___x_1250_);
v___x_1259_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1260_;
v___y_1146_ = v___x_1259_;
goto _start;
}
}
}
else
{
lean_object* v_out_1265_; lean_object* v_tagStack_1266_; lean_object* v_column_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v_indent_1165_);
v_out_1265_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1266_ = lean_ctor_get(v___y_1146_, 1);
v_column_1267_ = lean_ctor_get(v___y_1146_, 2);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1269_ = v___y_1146_;
v_isShared_1270_ = v_isSharedCheck_1284_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_column_1267_);
lean_inc(v_tagStack_1266_);
lean_inc(v_out_1265_);
lean_dec(v___y_1146_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1284_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_out_x27_1278_; lean_object* v___x_1280_; 
v___x_1271_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1272_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1271_, v_out_1265_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_add(v_column_1267_, v___x_1273_);
lean_dec(v_column_1267_);
v___x_1275_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1266_);
v___x_1276_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1266_, v_tagStack_1266_, v_activeTags_1166_, v___x_1275_);
v___x_1277_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1266_);
lean_dec(v_tagStack_1266_);
v_out_x27_1278_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1272_, v___x_1276_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 2, v___x_1274_);
lean_ctor_set(v___x_1269_, 1, v___x_1277_);
lean_ctor_set(v___x_1269_, 0, v_out_x27_1278_);
v___x_1280_ = v___x_1269_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_out_x27_1278_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v___x_1274_);
v___x_1280_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1281_;
v___y_1146_ = v___x_1280_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = l_Int_toNat(v_indent_1165_);
lean_dec(v_indent_1165_);
v___x_1286_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1158_);
lean_dec(v_fla_1158_);
if (v___x_1286_ == 0)
{
lean_object* v_out_1287_; lean_object* v_tagStack_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1306_; 
v_out_1287_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1288_ = lean_ctor_get(v___y_1146_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v___y_1146_, 2);
lean_dec(v_unused_1307_);
v___x_1290_ = v___y_1146_;
v_isShared_1291_ = v_isSharedCheck_1306_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_tagStack_1288_);
lean_inc(v_out_1287_);
lean_dec(v___y_1146_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1306_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_out_x27_1298_; lean_object* v___x_1300_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1285_);
v___x_1293_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1285_, v___x_1292_);
v___x_1294_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1293_, v_out_1287_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1288_);
v___x_1296_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1288_, v_tagStack_1288_, v_activeTags_1166_, v___x_1295_);
v___x_1297_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1288_);
lean_dec(v_tagStack_1288_);
v_out_x27_1298_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1294_, v___x_1296_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 2, v___x_1285_);
lean_ctor_set(v___x_1290_, 1, v___x_1297_);
lean_ctor_set(v___x_1290_, 0, v_out_x27_1298_);
v___x_1300_ = v___x_1290_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_out_x27_1298_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v___x_1285_);
v___x_1300_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; 
v___x_1301_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1159_, v_tail_1160_, v_tail_1154_, v_w_1144_, v___x_1300_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___x_1301_);
v_x_1145_ = v_fst_1302_;
v___y_1146_ = v_snd_1303_;
goto _start;
}
}
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_fst_1312_; 
v___x_1308_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0));
v___x_1309_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
v___x_1310_ = lean_nat_sub(v_w_1144_, v___x_1309_);
lean_inc(v_tail_1154_);
lean_inc(v_tail_1160_);
v___x_1311_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1159_, v_tail_1160_, v_tail_1154_, v___x_1310_, v___y_1146_);
lean_dec(v___x_1310_);
v_fst_1312_ = lean_ctor_get(v___x_1311_, 0);
if (lean_obj_tag(v_fst_1312_) == 1)
{
lean_object* v_head_1313_; lean_object* v_snd_1314_; lean_object* v_fla_1315_; uint8_t v___x_1316_; 
lean_inc_ref(v_fst_1312_);
v_head_1313_ = lean_ctor_get(v_fst_1312_, 0);
v_snd_1314_ = lean_ctor_get(v___x_1311_, 1);
lean_inc(v_snd_1314_);
lean_dec_ref(v___x_1311_);
v_fla_1315_ = lean_ctor_get(v_head_1313_, 0);
v___x_1316_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1315_);
if (v___x_1316_ == 0)
{
lean_object* v_out_1317_; lean_object* v_tagStack_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref_known(v_fst_1312_, 2);
v_out_1317_ = lean_ctor_get(v_snd_1314_, 0);
v_tagStack_1318_ = lean_ctor_get(v_snd_1314_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_snd_1314_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_snd_1314_, 2);
lean_dec(v_unused_1337_);
v___x_1320_ = v_snd_1314_;
v_isShared_1321_ = v_isSharedCheck_1336_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_tagStack_1318_);
lean_inc(v_out_1317_);
lean_dec(v_snd_1314_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1336_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_out_x27_1328_; lean_object* v___x_1330_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1285_);
v___x_1323_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1285_, v___x_1322_);
v___x_1324_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1323_, v_out_1317_);
v___x_1325_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1318_);
v___x_1326_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1318_, v_tagStack_1318_, v_activeTags_1166_, v___x_1325_);
v___x_1327_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1318_);
lean_dec(v_tagStack_1318_);
v_out_x27_1328_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1324_, v___x_1326_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 2, v___x_1285_);
lean_ctor_set(v___x_1320_, 1, v___x_1327_);
lean_ctor_set(v___x_1320_, 0, v_out_x27_1328_);
v___x_1330_ = v___x_1320_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_out_x27_1328_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v___x_1285_);
v___x_1330_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v_fst_1332_; lean_object* v_snd_1333_; 
v___x_1331_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1159_, v_tail_1160_, v_tail_1154_, v_w_1144_, v___x_1330_);
v_fst_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_fst_1332_);
v_snd_1333_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_snd_1333_);
lean_dec_ref(v___x_1331_);
v_x_1145_ = v_fst_1332_;
v___y_1146_ = v_snd_1333_;
goto _start;
}
}
}
else
{
lean_object* v_out_1338_; lean_object* v_tagStack_1339_; lean_object* v_column_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v___x_1285_);
lean_dec(v_tail_1160_);
lean_dec(v_tail_1154_);
v_out_1338_ = lean_ctor_get(v_snd_1314_, 0);
v_tagStack_1339_ = lean_ctor_get(v_snd_1314_, 1);
v_column_1340_ = lean_ctor_get(v_snd_1314_, 2);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_snd_1314_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1342_ = v_snd_1314_;
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_column_1340_);
lean_inc(v_tagStack_1339_);
lean_inc(v_out_1338_);
lean_dec(v_snd_1314_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_out_x27_1350_; lean_object* v___x_1352_; 
v___x_1344_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1308_, v_out_1338_);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_nat_add(v_column_1340_, v___x_1345_);
lean_dec(v_column_1340_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1339_);
v___x_1348_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1339_, v_tagStack_1339_, v_activeTags_1166_, v___x_1347_);
v___x_1349_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1339_);
lean_dec(v_tagStack_1339_);
v_out_x27_1350_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1344_, v___x_1348_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v___x_1346_);
lean_ctor_set(v___x_1342_, 1, v___x_1349_);
lean_ctor_set(v___x_1342_, 0, v_out_x27_1350_);
v___x_1352_ = v___x_1342_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_out_x27_1350_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v___x_1346_);
v___x_1352_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
v_x_1145_ = v_fst_1312_;
v___y_1146_ = v___x_1352_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v___x_1285_);
lean_dec(v_activeTags_1166_);
lean_dec(v_tail_1160_);
lean_dec(v_tail_1154_);
v_snd_1356_ = lean_ctor_get(v___x_1311_, 1);
lean_inc(v_snd_1356_);
lean_dec_ref(v___x_1311_);
v___x_1357_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2));
v___x_1358_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_1357_, v_snd_1356_);
return v___x_1358_;
}
}
}
}
case 2:
{
uint8_t v_force_1359_; uint8_t v___x_1360_; 
lean_del_object(v___x_1168_);
lean_del_object(v___x_1162_);
lean_del_object(v___x_1156_);
v_force_1359_ = lean_ctor_get_uint8(v_f_1164_, 0);
lean_dec_ref_known(v_f_1164_, 0);
v___x_1360_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1158_);
if (v___x_1360_ == 0)
{
v___y_1211_ = v___x_1360_;
goto v___jp_1210_;
}
else
{
if (v_force_1359_ == 0)
{
v___y_1211_ = v___x_1360_;
goto v___jp_1210_;
}
else
{
goto v___jp_1170_;
}
}
}
case 3:
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1156_);
v_a_1361_ = lean_ctor_get(v_f_1164_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_f_1164_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1363_ = v_f_1164_;
v_isShared_1364_ = v_isSharedCheck_1424_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v_f_1164_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1424_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint32_t v___x_1365_; lean_object* v_p_1366_; lean_object* v___x_1367_; uint8_t v_decide_1368_; 
v___x_1365_ = 10;
lean_inc_ref(v_a_1361_);
v_p_1366_ = lean_string_posof(v_a_1361_, v___x_1365_);
v___x_1367_ = lean_string_utf8_byte_size(v_a_1361_);
v_decide_1368_ = lean_nat_dec_eq(v_p_1366_, v___x_1367_);
if (v_decide_1368_ == 0)
{
lean_object* v_out_1369_; lean_object* v_tagStack_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1403_; 
v_out_1369_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1370_ = lean_ctor_get(v___y_1146_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v___y_1146_, 2);
lean_dec(v_unused_1404_);
v___x_1372_ = v___y_1146_;
v_isShared_1373_ = v_isSharedCheck_1403_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_tagStack_1370_);
lean_inc(v_out_1369_);
lean_dec(v___y_1146_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1403_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_string_utf8_extract(v_a_1361_, v___x_1374_, v_p_1366_);
v___x_1376_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1375_, v_out_1369_);
v___x_1377_ = l_Int_toNat(v_indent_1165_);
v___x_1378_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1377_);
v___x_1379_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1377_, v___x_1378_);
v___x_1380_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1379_, v___x_1376_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 2, v___x_1377_);
lean_ctor_set(v___x_1372_, 0, v___x_1380_);
v___x_1382_ = v___x_1372_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_tagStack_1370_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v___x_1377_);
v___x_1382_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = lean_string_utf8_next(v_a_1361_, v_p_1366_);
lean_dec(v_p_1366_);
v___x_1384_ = lean_string_utf8_extract(v_a_1361_, v___x_1383_, v___x_1367_);
lean_dec(v___x_1383_);
lean_dec_ref(v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1384_);
v___x_1386_ = v___x_1363_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1386_);
v___x_1388_ = v___x_1168_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_indent_1165_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_activeTags_1166_);
v___x_1388_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v_is_1390_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1388_);
v_is_1390_ = v___x_1162_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_tail_1160_);
v_is_1390_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_box(1);
v___x_1392_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1158_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v_fst_1394_; lean_object* v_snd_1395_; 
lean_dec(v_fla_1158_);
v___x_1393_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_1159_, v_is_1390_, v_tail_1154_, v_w_1144_, v___x_1382_);
v_fst_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_fst_1394_);
v_snd_1395_ = lean_ctor_get(v___x_1393_, 1);
lean_inc(v_snd_1395_);
lean_dec_ref(v___x_1393_);
v_x_1145_ = v_fst_1394_;
v___y_1146_ = v_snd_1395_;
goto _start;
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_is_1390_);
v_x_1145_ = v___x_1397_;
v___y_1146_ = v___x_1382_;
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
lean_object* v_out_1405_; lean_object* v_tagStack_1406_; lean_object* v_column_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_p_1366_);
lean_del_object(v___x_1363_);
lean_del_object(v___x_1168_);
lean_dec(v_indent_1165_);
lean_del_object(v___x_1162_);
v_out_1405_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1406_ = lean_ctor_get(v___y_1146_, 1);
v_column_1407_ = lean_ctor_get(v___y_1146_, 2);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1409_ = v___y_1146_;
v_isShared_1410_ = v_isSharedCheck_1423_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_column_1407_);
lean_inc(v_tagStack_1406_);
lean_inc(v_out_1405_);
lean_dec(v___y_1146_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1423_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_out_x27_1417_; lean_object* v___x_1419_; 
lean_inc_ref(v_a_1361_);
v___x_1411_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_1361_, v_out_1405_);
v___x_1412_ = lean_string_length(v_a_1361_);
lean_dec_ref(v_a_1361_);
v___x_1413_ = lean_nat_add(v_column_1407_, v___x_1412_);
lean_dec(v_column_1407_);
v___x_1414_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1406_);
v___x_1415_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1406_, v_tagStack_1406_, v_activeTags_1166_, v___x_1414_);
v___x_1416_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1406_);
lean_dec(v_tagStack_1406_);
v_out_x27_1417_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1411_, v___x_1415_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 2, v___x_1413_);
lean_ctor_set(v___x_1409_, 1, v___x_1416_);
lean_ctor_set(v___x_1409_, 0, v_out_x27_1417_);
v___x_1419_ = v___x_1409_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_out_x27_1417_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v___x_1413_);
v___x_1419_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1420_;
v___y_1146_ = v___x_1419_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1425_; lean_object* v_f_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_del_object(v___x_1156_);
v_indent_1425_ = lean_ctor_get(v_f_1164_, 0);
lean_inc(v_indent_1425_);
v_f_1426_ = lean_ctor_get(v_f_1164_, 1);
lean_inc(v_f_1426_);
lean_dec_ref_known(v_f_1164_, 2);
v___x_1427_ = lean_int_add(v_indent_1165_, v_indent_1425_);
lean_dec(v_indent_1425_);
lean_dec(v_indent_1165_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1427_);
lean_ctor_set(v___x_1168_, 0, v_f_1426_);
v___x_1429_ = v___x_1168_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_f_1426_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_activeTags_1166_);
v___x_1429_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1429_);
v___x_1431_ = v___x_1162_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_tail_1160_);
v___x_1431_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; 
v___x_1432_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v___x_1431_);
v_x_1145_ = v___x_1432_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1436_; lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v_a_1436_ = lean_ctor_get(v_f_1164_, 0);
lean_inc(v_a_1436_);
v_a_1437_ = lean_ctor_get(v_f_1164_, 1);
lean_inc(v_a_1437_);
lean_dec_ref_known(v_f_1164_, 2);
v___x_1438_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1165_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 2, v___x_1438_);
lean_ctor_set(v___x_1168_, 0, v_a_1436_);
v___x_1440_ = v___x_1168_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1436_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_indent_1165_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1441_, 0, v_a_1437_);
lean_ctor_set(v___x_1441_, 1, v_indent_1165_);
lean_ctor_set(v___x_1441_, 2, v_activeTags_1166_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1441_);
v___x_1443_ = v___x_1162_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_tail_1160_);
v___x_1443_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1443_);
lean_ctor_set(v___x_1156_, 0, v___x_1440_);
v___x_1445_ = v___x_1156_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v___x_1445_);
v_x_1145_ = v___x_1446_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1451_; uint8_t v_behavior_1452_; uint8_t v___x_1453_; 
lean_del_object(v___x_1156_);
v_a_1451_ = lean_ctor_get(v_f_1164_, 0);
lean_inc(v_a_1451_);
v_behavior_1452_ = lean_ctor_get_uint8(v_f_1164_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1164_, 1);
v___x_1453_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1158_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1455_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_a_1451_);
v___x_1455_ = v___x_1168_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1451_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_indent_1165_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_activeTags_1166_);
v___x_1455_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_box(0);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1456_);
lean_ctor_set(v___x_1162_, 0, v___x_1455_);
v___x_1458_ = v___x_1162_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_fst_1461_; lean_object* v_snd_1462_; 
v___x_1459_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v___x_1460_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_1452_, v___x_1458_, v___x_1459_, v_w_1144_, v___y_1146_);
v_fst_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_fst_1461_);
v_snd_1462_ = lean_ctor_get(v___x_1460_, 1);
lean_inc(v_snd_1462_);
lean_dec_ref(v___x_1460_);
v_x_1145_ = v_fst_1461_;
v___y_1146_ = v_snd_1462_;
goto _start;
}
}
}
else
{
lean_object* v___x_1467_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_a_1451_);
v___x_1467_ = v___x_1168_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1451_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_indent_1165_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_activeTags_1166_);
v___x_1467_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1467_);
v___x_1469_ = v___x_1162_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_tail_1160_);
v___x_1469_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v___x_1469_);
v_x_1145_ = v___x_1470_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1474_; lean_object* v_a_1475_; lean_object* v_out_1476_; lean_object* v_tagStack_1477_; lean_object* v_column_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1501_; 
v_a_1474_ = lean_ctor_get(v_f_1164_, 0);
lean_inc(v_a_1474_);
v_a_1475_ = lean_ctor_get(v_f_1164_, 1);
lean_inc(v_a_1475_);
lean_dec_ref_known(v_f_1164_, 2);
v_out_1476_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1477_ = lean_ctor_get(v___y_1146_, 1);
v_column_1478_ = lean_ctor_get(v___y_1146_, 2);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1480_ = v___y_1146_;
v_isShared_1481_ = v_isSharedCheck_1501_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_column_1478_);
lean_inc(v_tagStack_1477_);
lean_inc(v_out_1476_);
lean_dec(v___y_1146_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1501_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1482_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0));
lean_inc(v_column_1478_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_column_1478_);
lean_ctor_set(v___x_1483_, 1, v_out_1476_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_a_1474_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v_tagStack_1477_);
lean_ctor_set(v___x_1162_, 0, v___x_1484_);
v___x_1486_ = v___x_1162_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_tagStack_1477_);
v___x_1486_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1486_);
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1488_ = v___x_1480_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_column_1478_);
v___x_1488_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = lean_nat_add(v_activeTags_1166_, v___x_1489_);
lean_dec(v_activeTags_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 2, v___x_1490_);
lean_ctor_set(v___x_1168_, 0, v_a_1475_);
v___x_1492_ = v___x_1168_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1475_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_indent_1165_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v_tail_1160_);
lean_ctor_set(v___x_1156_, 0, v___x_1492_);
v___x_1494_ = v___x_1156_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_tail_1160_);
v___x_1494_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v___x_1494_);
v_x_1145_ = v___x_1495_;
v___y_1146_ = v___x_1488_;
goto _start;
}
}
}
}
}
}
}
v___jp_1170_:
{
lean_object* v_out_1171_; lean_object* v_tagStack_1172_; lean_object* v_column_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1209_; 
v_out_1171_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1172_ = lean_ctor_get(v___y_1146_, 1);
v_column_1173_ = lean_ctor_get(v___y_1146_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1175_ = v___y_1146_;
v_isShared_1176_ = v_isSharedCheck_1209_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_column_1173_);
lean_inc(v_tagStack_1172_);
lean_inc(v_out_1171_);
lean_dec(v___y_1146_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1209_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
lean_inc(v_column_1173_);
v___x_1177_ = lean_nat_to_int(v_column_1173_);
v___x_1178_ = lean_int_dec_lt(v___x_1177_, v_indent_1165_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_out_x27_1186_; lean_object* v___x_1188_; 
lean_dec(v___x_1177_);
lean_dec(v_column_1173_);
v___x_1179_ = l_Int_toNat(v_indent_1165_);
lean_dec(v_indent_1165_);
v___x_1180_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0));
lean_inc(v___x_1179_);
v___x_1181_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_1179_, v___x_1180_);
v___x_1182_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1181_, v_out_1171_);
v___x_1183_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1172_);
v___x_1184_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1172_, v_tagStack_1172_, v_activeTags_1166_, v___x_1183_);
v___x_1185_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1172_);
lean_dec(v_tagStack_1172_);
v_out_x27_1186_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1182_, v___x_1184_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 2, v___x_1179_);
lean_ctor_set(v___x_1175_, 1, v___x_1185_);
lean_ctor_set(v___x_1175_, 0, v_out_x27_1186_);
v___x_1188_ = v___x_1175_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_out_x27_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v___x_1179_);
v___x_1188_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1189_;
v___y_1146_ = v___x_1188_;
goto _start;
}
}
else
{
lean_object* v___x_1192_; uint32_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v_out_x27_1203_; lean_object* v___x_1205_; 
v___x_1192_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_1193_ = 32;
v___x_1194_ = lean_int_sub(v_indent_1165_, v___x_1177_);
lean_dec(v___x_1177_);
lean_dec(v_indent_1165_);
v___x_1195_ = l_Int_toNat(v___x_1194_);
lean_dec(v___x_1194_);
v___x_1196_ = lean_string_pushn(v___x_1192_, v___x_1193_, v___x_1195_);
lean_inc_ref(v___x_1196_);
v___x_1197_ = l_Lean_Widget_TaggedText_appendText___redArg(v___x_1196_, v_out_1171_);
v___x_1198_ = lean_string_length(v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1199_ = lean_nat_add(v_column_1173_, v___x_1198_);
lean_dec(v_column_1173_);
v___x_1200_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1172_);
v___x_1201_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1172_, v_tagStack_1172_, v_activeTags_1166_, v___x_1200_);
v___x_1202_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1172_);
lean_dec(v_tagStack_1172_);
v_out_x27_1203_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_1197_, v___x_1201_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 2, v___x_1199_);
lean_ctor_set(v___x_1175_, 1, v___x_1202_);
lean_ctor_set(v___x_1175_, 0, v_out_x27_1203_);
v___x_1205_ = v___x_1175_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_out_x27_1203_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v___x_1199_);
v___x_1205_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1206_;
v___y_1146_ = v___x_1205_;
goto _start;
}
}
}
}
v___jp_1210_:
{
if (v___y_1211_ == 0)
{
goto v___jp_1170_;
}
else
{
lean_object* v_out_1212_; lean_object* v_tagStack_1213_; lean_object* v_column_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_indent_1165_);
v_out_1212_ = lean_ctor_get(v___y_1146_, 0);
v_tagStack_1213_ = lean_ctor_get(v___y_1146_, 1);
v_column_1214_ = lean_ctor_get(v___y_1146_, 2);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___y_1146_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1216_ = v___y_1146_;
v_isShared_1217_ = v_isSharedCheck_1227_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_column_1214_);
lean_inc(v_tagStack_1213_);
lean_inc(v_out_1212_);
lean_dec(v___y_1146_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1227_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_out_x27_1221_; lean_object* v___x_1223_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0));
lean_inc(v_activeTags_1166_);
lean_inc(v_tagStack_1213_);
v___x_1219_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_tagStack_1213_, v_tagStack_1213_, v_activeTags_1166_, v___x_1218_);
v___x_1220_ = l_List_drop___redArg(v_activeTags_1166_, v_tagStack_1213_);
lean_dec(v_tagStack_1213_);
v_out_x27_1221_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_1212_, v___x_1219_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___x_1220_);
lean_ctor_set(v___x_1216_, 0, v_out_x27_1221_);
v___x_1223_ = v___x_1216_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_out_x27_1221_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_column_1214_);
v___x_1223_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; 
v___x_1224_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_1158_, v_flb_1159_, v_tail_1154_, v_tail_1160_);
v_x_1145_ = v___x_1224_;
v___y_1146_ = v___x_1223_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(lean_object* v_w_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1507_, v_x_1508_, v___y_1509_);
lean_dec(v_w_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(lean_object* v_f_1511_, lean_object* v_w_1512_, lean_object* v_indent_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1515_ = lean_box(1);
v___x_1516_ = 0;
v___x_1517_ = lean_nat_to_int(v_indent_1513_);
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1519_, 0, v_f_1511_);
lean_ctor_set(v___x_1519_, 1, v___x_1517_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1522_, 0, v___x_1515_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_ctor_set_uint8(v___x_1522_, sizeof(void*)*2, v___x_1516_);
v___x_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1520_);
v___x_1524_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_1512_, v___x_1523_, v___y_1514_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(lean_object* v_f_1525_, lean_object* v_w_1526_, lean_object* v_indent_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1525_, v_w_1526_, v_indent_1527_, v___y_1528_);
lean_dec(v_w_1526_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object* v_f_1530_, lean_object* v_indent_1531_, lean_object* v_w_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_snd_1535_; lean_object* v_out_1536_; 
v___x_1533_ = ((lean_object*)(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1));
v___x_1534_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(v_f_1530_, v_w_1532_, v_indent_1531_, v___x_1533_);
v_snd_1535_ = lean_ctor_get(v___x_1534_, 1);
lean_inc(v_snd_1535_);
lean_dec_ref(v___x_1534_);
v_out_1536_ = lean_ctor_get(v_snd_1535_, 0);
lean_inc_ref(v_out_1536_);
lean_dec(v_snd_1535_);
return v_out_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_prettyTagged___boxed(lean_object* v_f_1537_, lean_object* v_indent_1538_, lean_object* v_w_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_1537_, v_indent_1538_, v_w_1539_);
lean_dec(v_w_1539_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_nat_to_int(v_a_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(lean_object* v_acc_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = lean_array_get_size(v_a_1544_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_nat_dec_eq(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = lean_obj_once(&l_Lean_Widget_instInhabitedTaggedText_default___closed__0, &l_Lean_Widget_instInhabitedTaggedText_default___closed__0_once, _init_l_Lean_Widget_instInhabitedTaggedText_default___closed__0);
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_sub(v___x_1545_, v___x_1549_);
v___x_1551_ = lean_array_get_borrowed(v___x_1548_, v_a_1544_, v___x_1550_);
switch(lean_obj_tag(v___x_1551_))
{
case 0:
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v___x_1550_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v___x_1553_ = lean_string_append(v_acc_1543_, v_a_1552_);
v___x_1554_ = lean_array_pop(v_a_1544_);
v_acc_1543_ = v___x_1553_;
v_a_1544_ = v___x_1554_;
goto _start;
}
case 1:
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v___x_1550_);
v_a_1556_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_a_1556_);
v___x_1557_ = lean_array_pop(v_a_1544_);
v___x_1558_ = l_Array_reverse___redArg(v_a_1556_);
v___x_1559_ = l_Array_append___redArg(v___x_1557_, v___x_1558_);
lean_dec_ref(v___x_1558_);
v_a_1544_ = v___x_1559_;
goto _start;
}
default: 
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1551_, 1);
lean_inc_ref(v_a_1561_);
v___x_1562_ = lean_array_set(v_a_1544_, v___x_1550_, v_a_1561_);
lean_dec(v___x_1550_);
v_a_1544_ = v___x_1562_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_1544_);
return v_acc_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(lean_object* v_00_u03b1_1564_, lean_object* v_acc_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v_acc_1565_, v_a_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object* v_tt_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1569_ = ((lean_object*)(l_Lean_Widget_instInhabitedTaggedText_default___redArg___closed__0));
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_mk_empty_array_with_capacity(v___x_1570_);
v___x_1572_ = lean_array_push(v___x_1571_, v_tt_1568_);
v___x_1573_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(v___x_1569_, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_stripTags(lean_object* v_00_u03b1_1574_, lean_object* v_tt_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1575_);
return v___x_1576_;
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

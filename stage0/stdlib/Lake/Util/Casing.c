// Lean compiler output
// Module: Lake.Util.Casing
// Imports: public import Init.Data.String.Basic import Init.Data.String.Modify import Init.Data.String.Search
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
static lean_object* l_Lake_toUpperCamelCaseString___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___lam__0(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___lam__0___boxed(lean_object*);
uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_toUpperCamelCaseString___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Lake_toUpperCamelCaseString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 95;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 45;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___lam__0___boxed), 1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_nat_sub(x_24, x_23);
x_26 = lean_nat_dec_eq(x_20, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_nat_add(x_23, x_20);
x_28 = lean_string_utf8_next_fast(x_22, x_27);
x_29 = lean_nat_sub(x_28, x_23);
lean_dec(x_28);
lean_inc_ref(x_21);
lean_inc(x_29);
lean_ctor_set(x_17, 0, x_29);
x_30 = lean_string_utf8_get_fast(x_22, x_27);
lean_dec(x_27);
x_31 = lean_box_uint32(x_30);
x_32 = lean_apply_1(x_21, x_31);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_dec(x_29);
lean_dec(x_20);
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_1);
x_35 = l_String_Slice_slice_x21(x_1, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_36 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 2);
lean_inc(x_38);
lean_dec_ref(x_35);
lean_ctor_set(x_2, 0, x_29);
x_4 = x_2;
x_5 = x_36;
x_6 = x_37;
x_7 = x_38;
goto block_15;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_17);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_free_object(x_2);
x_39 = lean_nat_add(x_23, x_19);
lean_dec(x_19);
x_40 = lean_box(1);
lean_inc(x_24);
lean_inc_ref(x_22);
x_4 = x_40;
x_5 = x_22;
x_6 = x_39;
x_7 = x_24;
goto block_15;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_nat_sub(x_46, x_45);
x_48 = lean_nat_dec_eq(x_42, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_nat_add(x_45, x_42);
x_50 = lean_string_utf8_next_fast(x_44, x_49);
x_51 = lean_nat_sub(x_50, x_45);
lean_dec(x_50);
lean_inc_ref(x_43);
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
x_53 = lean_string_utf8_get_fast(x_44, x_49);
lean_dec(x_49);
x_54 = lean_box_uint32(x_53);
x_55 = lean_apply_1(x_43, x_54);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_dec(x_51);
lean_dec(x_42);
lean_ctor_set(x_2, 1, x_52);
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_inc_ref(x_1);
x_58 = l_String_Slice_slice_x21(x_1, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_59 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
lean_dec_ref(x_58);
lean_ctor_set(x_2, 1, x_52);
lean_ctor_set(x_2, 0, x_51);
x_4 = x_2;
x_5 = x_59;
x_6 = x_60;
x_7 = x_61;
goto block_15;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_43);
lean_dec(x_42);
lean_free_object(x_2);
x_62 = lean_nat_add(x_45, x_41);
lean_dec(x_41);
x_63 = lean_box(1);
lean_inc(x_46);
lean_inc_ref(x_44);
x_4 = x_63;
x_5 = x_44;
x_6 = x_62;
x_7 = x_46;
goto block_15;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_2, 1);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_1, 0);
x_70 = lean_ctor_get(x_1, 1);
x_71 = lean_ctor_get(x_1, 2);
x_72 = lean_nat_sub(x_71, x_70);
x_73 = lean_nat_dec_eq(x_66, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint32_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_nat_add(x_70, x_66);
x_75 = lean_string_utf8_next_fast(x_69, x_74);
x_76 = lean_nat_sub(x_75, x_70);
lean_dec(x_75);
lean_inc_ref(x_67);
lean_inc(x_76);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_67);
x_78 = lean_string_utf8_get_fast(x_69, x_74);
lean_dec(x_74);
x_79 = lean_box_uint32(x_78);
x_80 = lean_apply_1(x_67, x_79);
x_81 = lean_unbox(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_76);
lean_dec(x_66);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_77);
x_2 = x_82;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc_ref(x_1);
x_84 = l_String_Slice_slice_x21(x_1, x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
x_85 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 2);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_77);
x_4 = x_88;
x_5 = x_85;
x_6 = x_86;
x_7 = x_87;
goto block_15;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
x_89 = lean_nat_add(x_70, x_65);
lean_dec(x_65);
x_90 = lean_box(1);
lean_inc(x_71);
lean_inc_ref(x_69);
x_4 = x_90;
x_5 = x_69;
x_6 = x_89;
x_7 = x_71;
goto block_15;
}
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
block_15:
{
lean_object* x_8; lean_object* x_9; uint32_t x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_get(x_8, x_9);
x_11 = l_Char_toUpper(x_10);
x_12 = lean_string_utf8_set(x_8, x_9, x_11);
x_13 = lean_array_push(x_3, x_12);
x_2 = x_4;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Lake_toUpperCamelCaseString_spec__1___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lake_toUpperCamelCaseString___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_toUpperCamelCaseString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(x_4);
x_6 = l_Lake_toUpperCamelCaseString___closed__0;
x_7 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Lake_toUpperCamelCaseString_spec__1___redArg(x_4, x_5, x_6);
x_8 = lean_array_to_list(x_7);
x_9 = l_Lake_toUpperCamelCaseString___closed__1;
x_10 = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(x_9, x_8);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_toUpperCamelCase(x_2);
x_5 = l_Lake_toUpperCamelCaseString(x_3);
x_6 = l_Lean_Name_str___override(x_4, x_5);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Casing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_toUpperCamelCaseString___closed__0 = _init_l_Lake_toUpperCamelCaseString___closed__0();
lean_mark_persistent(l_Lake_toUpperCamelCaseString___closed__0);
l_Lake_toUpperCamelCaseString___closed__1 = _init_l_Lake_toUpperCamelCaseString___closed__1();
lean_mark_persistent(l_Lake_toUpperCamelCaseString___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

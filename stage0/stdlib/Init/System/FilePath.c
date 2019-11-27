// Lean compiler output
// Module: Init.System.FilePath
// Imports: Init.System.Platform Init.Data.String.Basic
#include "runtime/lean.h"
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
lean_object* l_List_reverse___rarg(lean_object*);
extern uint8_t l_System_Platform_isWindows;
extern uint8_t l_System_Platform_isOSX;
lean_object* l_System_FilePath_searchPathSeparators___closed__1___boxed__const__1;
lean_object* l_String_revPosOf(lean_object*, uint32_t);
uint8_t l_System_FilePath_isCaseInsensitive;
lean_object* l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_System_FilePath_splitSearchPath(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_System_FilePath_searchPathSeparators___closed__2;
lean_object* l_System_FilePath_pathSeparators;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_System_FilePath_searchPathSeparators___closed__2___boxed__const__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_normalizePath___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalizePath___closed__1;
lean_object* l_String_splitAux___main___at_System_FilePath_splitSearchPath___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_splitSearchPath___boxed(lean_object*);
lean_object* l_System_FilePath_searchPathSeparators___closed__1;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_System_FilePath_normalizePath(lean_object*);
uint32_t l_System_FilePath_pathSeparator___closed__2;
lean_object* l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathSeparator___closed__1;
uint32_t l_System_FilePath_pathSeparator;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t l_System_FilePath_isCaseInsensitive___closed__1;
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2(lean_object*);
uint32_t l_System_FilePath_searchPathSeparator___closed__1;
lean_object* l_System_FilePath_searchPathSeparators;
uint8_t l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(uint32_t, uint8_t, lean_object*);
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2___boxed(lean_object*);
uint32_t l_System_FilePath_extSeparator;
lean_object* l_String_splitAux___main___at_System_FilePath_splitSearchPath___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_System_FilePath_searchPathSeparator;
lean_object* l_System_FilePath_pathSeparators___closed__3;
uint8_t l_Char_DecidableEq(uint32_t, uint32_t);
lean_object* l_System_FilePath_searchPathSeparators___closed__3;
lean_object* l_System_FilePath_pathSeparators___closed__2;
uint8_t l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1(uint32_t, lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__1;
lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_List_foldr___main___at_System_FilePath_normalizePath___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint8_t _init_l_System_FilePath_pathSeparator___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; 
x_1 = l_System_Platform_isWindows;
x_2 = 1;
x_3 = l_Bool_DecidableEq(x_1, x_2);
return x_3;
}
}
uint32_t _init_l_System_FilePath_pathSeparator___closed__2() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 92;
return x_3;
}
}
}
uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__2;
return x_1;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators___closed__1;
x_2 = l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__3() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__2;
return x_3;
}
}
}
lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_pathSeparators___closed__3;
return x_1;
}
}
uint32_t _init_l_System_FilePath_searchPathSeparator___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 59;
return x_3;
}
}
}
uint32_t _init_l_System_FilePath_searchPathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_searchPathSeparator___closed__1;
return x_1;
}
}
lean_object* _init_l_System_FilePath_searchPathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 58;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l_System_FilePath_searchPathSeparators___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_System_FilePath_searchPathSeparators___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_System_FilePath_searchPathSeparators___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 59;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l_System_FilePath_searchPathSeparators___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_searchPathSeparators___closed__1;
x_2 = l_System_FilePath_searchPathSeparators___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_System_FilePath_searchPathSeparators___closed__3() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_FilePath_searchPathSeparators___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_searchPathSeparators___closed__2;
return x_3;
}
}
}
lean_object* _init_l_System_FilePath_searchPathSeparators() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_searchPathSeparators___closed__3;
return x_1;
}
}
uint8_t l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1(uint32_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = l_Char_DecidableEq(x_1, x_6);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_String_splitAux___main___at_System_FilePath_splitSearchPath___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_1, x_3);
x_9 = l_System_FilePath_searchPathSeparators;
x_10 = l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1(x_8, x_9);
x_11 = l_Bool_DecidableEq(x_10, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_14, x_15);
x_17 = lean_string_utf8_extract(x_1, x_2, x_16);
lean_dec(x_16);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
lean_inc(x_14);
x_2 = x_14;
x_3 = x_14;
x_4 = x_18;
goto _start;
}
}
else
{
uint32_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_20 = lean_string_utf8_get(x_1, x_3);
x_21 = l_System_FilePath_searchPathSeparators;
x_22 = l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1(x_20, x_21);
x_23 = l_Bool_DecidableEq(x_22, x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
x_26 = l_List_reverse___rarg(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_3, x_27);
lean_dec(x_3);
x_29 = lean_string_utf8_extract(x_1, x_2, x_28);
lean_dec(x_28);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
x_31 = l_String_splitAux___main___closed__1;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_reverse___rarg(x_32);
return x_33;
}
}
}
}
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___main___at_System_FilePath_splitSearchPath___spec__3(x_1, x_3, x_3, x_2);
return x_4;
}
}
lean_object* l_System_FilePath_splitSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_System_FilePath_splitSearchPath___spec__2(x_1);
return x_2;
}
}
lean_object* l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_List_elem___main___at_System_FilePath_splitSearchPath___spec__1(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_String_splitAux___main___at_System_FilePath_splitSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___main___at_System_FilePath_splitSearchPath___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_System_FilePath_splitSearchPath___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_System_FilePath_splitSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_splitSearchPath(x_1);
lean_dec(x_1);
return x_2;
}
}
uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
uint32_t x_1; 
x_1 = 46;
return x_1;
}
}
uint8_t _init_l_System_FilePath_isCaseInsensitive___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
uint8_t _init_l_System_FilePath_isCaseInsensitive() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_isCaseInsensitive___closed__1;
return x_1;
}
}
uint8_t l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(uint32_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint32_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(x_1, x_2, x_5);
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_Char_DecidableEq(x_1, x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
x_4 = 1;
x_5 = l_Bool_DecidableEq(x_3, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_string_utf8_get(x_2, x_1);
x_7 = 0;
x_8 = l_System_FilePath_pathSeparators;
x_9 = l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(x_6, x_7, x_8);
x_10 = l_Bool_DecidableEq(x_9, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_set(x_2, x_1, x_6);
x_12 = lean_string_utf8_next(x_11, x_1);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_11;
goto _start;
}
else
{
uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_System_FilePath_pathSeparator;
x_15 = lean_string_utf8_set(x_2, x_1, x_14);
x_16 = lean_string_utf8_next(x_15, x_1);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_15;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* _init_l_System_FilePath_normalizePath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
uint8_t _init_l_System_FilePath_normalizePath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_System_FilePath_normalizePath___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_System_FilePath_normalizePath(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; 
x_8 = l_System_FilePath_normalizePath___closed__2;
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
x_2 = x_9;
goto block_7;
}
else
{
uint8_t x_10; 
x_10 = l_System_FilePath_isCaseInsensitive;
if (x_10 == 0)
{
x_2 = x_8;
goto block_7;
}
else
{
uint8_t x_11; 
x_11 = 0;
x_2 = x_11;
goto block_7;
}
}
block_7:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 1;
x_4 = l_Bool_DecidableEq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(x_5, x_1);
return x_6;
}
else
{
return x_1;
}
}
}
}
lean_object* l_List_foldr___main___at_System_FilePath_normalizePath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(x_4, x_5, x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* _init_l_System_FilePath_dirName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
lean_object* l_System_FilePath_dirName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_2 = l_System_FilePath_normalizePath(x_1);
x_3 = l_System_FilePath_pathSeparator;
x_4 = l_String_revPosOf(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_System_FilePath_dirName___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_extract(x_2, x_7, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
}
lean_object* initialize_Init_System_Platform(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_FilePath(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Platform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_FilePath_pathSeparator___closed__1 = _init_l_System_FilePath_pathSeparator___closed__1();
l_System_FilePath_pathSeparator___closed__2 = _init_l_System_FilePath_pathSeparator___closed__2();
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators___closed__2___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__2___boxed__const__1);
l_System_FilePath_pathSeparators___closed__2 = _init_l_System_FilePath_pathSeparators___closed__2();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__2);
l_System_FilePath_pathSeparators___closed__3 = _init_l_System_FilePath_pathSeparators___closed__3();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__3);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_searchPathSeparator___closed__1 = _init_l_System_FilePath_searchPathSeparator___closed__1();
l_System_FilePath_searchPathSeparator = _init_l_System_FilePath_searchPathSeparator();
l_System_FilePath_searchPathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_searchPathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_searchPathSeparators___closed__1___boxed__const__1);
l_System_FilePath_searchPathSeparators___closed__1 = _init_l_System_FilePath_searchPathSeparators___closed__1();
lean_mark_persistent(l_System_FilePath_searchPathSeparators___closed__1);
l_System_FilePath_searchPathSeparators___closed__2___boxed__const__1 = _init_l_System_FilePath_searchPathSeparators___closed__2___boxed__const__1();
lean_mark_persistent(l_System_FilePath_searchPathSeparators___closed__2___boxed__const__1);
l_System_FilePath_searchPathSeparators___closed__2 = _init_l_System_FilePath_searchPathSeparators___closed__2();
lean_mark_persistent(l_System_FilePath_searchPathSeparators___closed__2);
l_System_FilePath_searchPathSeparators___closed__3 = _init_l_System_FilePath_searchPathSeparators___closed__3();
lean_mark_persistent(l_System_FilePath_searchPathSeparators___closed__3);
l_System_FilePath_searchPathSeparators = _init_l_System_FilePath_searchPathSeparators();
lean_mark_persistent(l_System_FilePath_searchPathSeparators);
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_isCaseInsensitive___closed__1 = _init_l_System_FilePath_isCaseInsensitive___closed__1();
l_System_FilePath_isCaseInsensitive = _init_l_System_FilePath_isCaseInsensitive();
l_System_FilePath_normalizePath___closed__1 = _init_l_System_FilePath_normalizePath___closed__1();
lean_mark_persistent(l_System_FilePath_normalizePath___closed__1);
l_System_FilePath_normalizePath___closed__2 = _init_l_System_FilePath_normalizePath___closed__2();
l_System_FilePath_dirName___closed__1 = _init_l_System_FilePath_dirName___closed__1();
lean_mark_persistent(l_System_FilePath_dirName___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

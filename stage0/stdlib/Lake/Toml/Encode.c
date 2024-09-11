// Lean compiler output
// Module: Lake.Toml.Encode
// Imports: Init Lake.Toml.Data Lake.Util.FilePath
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
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertIf___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlInt(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlValue;
LEAN_EXPORT lean_object* l_Lake_instToTomlTable;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1(lean_object*);
static lean_object* l_Lake_instToTomlValue___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlBool(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertSome(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlFilePath(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertUnless___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlNat(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instToTomlName___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertArrayOfToToml___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object*);
static lean_object* l_Lake_Toml_Table_insert___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertIf___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlName___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_Value_table(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertIf(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object*);
lean_object* l_Lake_Toml_RBDict_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertUnless___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertUnless(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___boxed(lean_object*);
static lean_object* l_Lake_instToTomlTable___closed__1;
LEAN_EXPORT lean_object* l_Lake_instToTomlString(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertArrayOfToToml(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_instToTomlName___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertSome___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsert(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat(double);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___rarg(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lake_instToTomlValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToTomlValue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToTomlValue___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_mkRelPathString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instToTomlName___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_instToTomlName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToTomlName___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lake_instToTomlName___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlName___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_instToTomlName___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_nat_to_int(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat(double x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_float(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = l_Lake_instToTomlFloat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_instToTomlBool(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg(x_1, x_3, x_4, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToTomlArray___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_instToTomlArray___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_instToTomlTable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Value_table), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToTomlTable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToTomlTable___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_Table_insert___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_7 = l_Lake_Toml_RBDict_insert___rarg(x_6, x_2, x_5, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_insert___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertSome___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_5);
x_7 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_8 = l_Lake_Toml_RBDict_insert___rarg(x_7, x_2, x_6, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertSome(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_insertSome___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_insertSome___rarg), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_smartInsert___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Array_isEmpty___rarg(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_9 = l_Lake_Toml_RBDict_insert___rarg(x_8, x_1, x_7, x_3);
return x_9;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertArrayOfToToml___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_3);
x_7 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_8 = l_Lake_Toml_RBDict_insert___rarg(x_7, x_2, x_6, x_4);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertArrayOfToToml(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertArrayOfToToml___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_10 = l_Lake_Toml_RBDict_insert___rarg(x_9, x_1, x_8, x_3);
return x_10;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertIf___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_2 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_8 = l_Lake_Toml_RBDict_insert___rarg(x_7, x_3, x_6, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertIf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_insertIf___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertIf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_Toml_Table_insertIf___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertUnless___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_2 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_8 = l_Lake_Toml_RBDict_insert___rarg(x_7, x_3, x_6, x_5);
return x_8;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertUnless(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_insertUnless___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertUnless___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_Toml_Table_insertUnless___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_7 = lean_apply_2(x_2, x_4, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_1(x_1, x_4);
x_10 = l_Lake_Toml_Table_insert___rarg___closed__1;
x_11 = l_Lake_Toml_RBDict_insert___rarg(x_10, x_3, x_9, x_6);
return x_11;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_insertD___rarg), 6, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Data(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Encode(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instToTomlValue___closed__1 = _init_l_Lake_instToTomlValue___closed__1();
lean_mark_persistent(l_Lake_instToTomlValue___closed__1);
l_Lake_instToTomlValue = _init_l_Lake_instToTomlValue();
lean_mark_persistent(l_Lake_instToTomlValue);
l_Lake_instToTomlName___closed__1 = _init_l_Lake_instToTomlName___closed__1();
lean_mark_persistent(l_Lake_instToTomlName___closed__1);
l_Lake_instToTomlTable___closed__1 = _init_l_Lake_instToTomlTable___closed__1();
lean_mark_persistent(l_Lake_instToTomlTable___closed__1);
l_Lake_instToTomlTable = _init_l_Lake_instToTomlTable();
lean_mark_persistent(l_Lake_instToTomlTable);
l_Lake_Toml_Table_insert___rarg___closed__1 = _init_l_Lake_Toml_Table_insert___rarg___closed__1();
lean_mark_persistent(l_Lake_Toml_Table_insert___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

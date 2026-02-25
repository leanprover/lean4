// Lean compiler output
// Module: Lake.Version
// Imports: public import Init.Prelude import Init.Data.ToString import Init.Data.String.TakeDrop
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
LEAN_EXPORT lean_object* l_Lake_version_major;
LEAN_EXPORT lean_object* l_Lake_version_minor;
LEAN_EXPORT lean_object* l_Lake_version_patch;
extern uint8_t l_Lean_version_isRelease;
LEAN_EXPORT uint8_t l_Lake_version_isRelease;
static const lean_string_object l_Lake_version_specialDesc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* l_Lake_version_specialDesc___closed__0 = (const lean_object*)&l_Lake_version_specialDesc___closed__0_value;
static const lean_string_object l_Lake_version_specialDesc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "src+"};
static const lean_object* l_Lake_version_specialDesc___closed__1 = (const lean_object*)&l_Lake_version_specialDesc___closed__1_value;
extern lean_object* l_Lean_githash;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_Lake_version_specialDesc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__2;
static lean_once_cell_t l_Lake_version_specialDesc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__3;
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_version_specialDesc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__4;
static lean_once_cell_t l_Lake_version_specialDesc___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__5;
lean_object* l_String_Slice_toString(lean_object*);
static lean_once_cell_t l_Lake_version_specialDesc___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_version_specialDesc___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_version_specialDesc___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_version_specialDesc___closed__8;
LEAN_EXPORT lean_object* l_Lake_version_specialDesc;
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l_Lake_versionStringCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__0;
static const lean_string_object l_Lake_versionStringCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_versionStringCore___closed__1 = (const lean_object*)&l_Lake_versionStringCore___closed__1_value;
static lean_once_cell_t l_Lake_versionStringCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__2;
static lean_once_cell_t l_Lake_versionStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__3;
static lean_once_cell_t l_Lake_versionStringCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__4;
static lean_once_cell_t l_Lake_versionStringCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__5;
static lean_once_cell_t l_Lake_versionStringCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__6;
LEAN_EXPORT lean_object* l_Lake_versionStringCore;
static const lean_string_object l_Lake_versionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_versionString___closed__0 = (const lean_object*)&l_Lake_versionString___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_versionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_versionString___closed__1;
static const lean_string_object l_Lake_versionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_versionString___closed__2 = (const lean_object*)&l_Lake_versionString___closed__2_value;
static lean_once_cell_t l_Lake_versionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionString___closed__3;
static lean_once_cell_t l_Lake_versionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionString___closed__4;
LEAN_EXPORT lean_object* l_Lake_versionString;
static const lean_string_object l_Lake_uiVersionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lake version "};
static const lean_object* l_Lake_uiVersionString___closed__0 = (const lean_object*)&l_Lake_uiVersionString___closed__0_value;
static lean_once_cell_t l_Lake_uiVersionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__1;
static const lean_string_object l_Lake_uiVersionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " (Lean version "};
static const lean_object* l_Lake_uiVersionString___closed__2 = (const lean_object*)&l_Lake_uiVersionString___closed__2_value;
static lean_once_cell_t l_Lake_uiVersionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__3;
extern lean_object* l_Lean_versionString;
static lean_once_cell_t l_Lake_uiVersionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__4;
static const lean_string_object l_Lake_uiVersionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake_uiVersionString___closed__5 = (const lean_object*)&l_Lake_uiVersionString___closed__5_value;
static lean_once_cell_t l_Lake_uiVersionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__6;
LEAN_EXPORT lean_object* l_Lake_uiVersionString;
static lean_object* _init_l_Lake_version_major(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(5u);
return x_1;
}
}
static lean_object* _init_l_Lake_version_minor(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lake_version_patch(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static uint8_t _init_l_Lake_version_isRelease(void) {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
return x_1;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_githash;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lake_version_specialDesc___closed__2, &l_Lake_version_specialDesc___closed__2_once, _init_l_Lake_version_specialDesc___closed__2);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_githash;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lake_version_specialDesc___closed__3, &l_Lake_version_specialDesc___closed__3_once, _init_l_Lake_version_specialDesc___closed__3);
x_4 = l_String_Slice_Pos_nextn(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lake_version_specialDesc___closed__4, &l_Lake_version_specialDesc___closed__4_once, _init_l_Lake_version_specialDesc___closed__4);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_githash;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lake_version_specialDesc___closed__5, &l_Lake_version_specialDesc___closed__5_once, _init_l_Lake_version_specialDesc___closed__5);
x_2 = l_String_Slice_toString(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lake_version_specialDesc___closed__6, &l_Lake_version_specialDesc___closed__6_once, _init_l_Lake_version_specialDesc___closed__6);
x_2 = ((lean_object*)(l_Lake_version_specialDesc___closed__1));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_version_specialDesc___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_Lake_version_specialDesc___closed__2, &l_Lake_version_specialDesc___closed__2_once, _init_l_Lake_version_specialDesc___closed__2);
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_version_specialDesc(void) {
_start:
{
uint8_t x_1; uint8_t x_5; 
x_5 = l_Lean_version_isRelease;
if (x_5 == 0)
{
x_1 = x_5;
goto block_4;
}
else
{
uint8_t x_6; 
x_6 = lean_uint8_once(&l_Lake_version_specialDesc___closed__8, &l_Lake_version_specialDesc___closed__8_once, _init_l_Lake_version_specialDesc___closed__8);
if (x_6 == 0)
{
x_1 = x_5;
goto block_4;
}
else
{
lean_object* x_7; 
x_7 = ((lean_object*)(l_Lake_version_specialDesc___closed__0));
return x_7;
}
}
block_4:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lake_version_specialDesc___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Lake_version_specialDesc___closed__7, &l_Lake_version_specialDesc___closed__7_once, _init_l_Lake_version_specialDesc___closed__7);
return x_3;
}
}
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_versionStringCore___closed__1));
x_2 = lean_obj_once(&l_Lake_versionStringCore___closed__0, &l_Lake_versionStringCore___closed__0_once, _init_l_Lake_versionStringCore___closed__0);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lake_versionStringCore___closed__3, &l_Lake_versionStringCore___closed__3_once, _init_l_Lake_versionStringCore___closed__3);
x_2 = lean_obj_once(&l_Lake_versionStringCore___closed__2, &l_Lake_versionStringCore___closed__2_once, _init_l_Lake_versionStringCore___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_versionStringCore___closed__1));
x_2 = lean_obj_once(&l_Lake_versionStringCore___closed__4, &l_Lake_versionStringCore___closed__4_once, _init_l_Lake_versionStringCore___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lake_versionStringCore___closed__3, &l_Lake_versionStringCore___closed__3_once, _init_l_Lake_versionStringCore___closed__3);
x_2 = lean_obj_once(&l_Lake_versionStringCore___closed__5, &l_Lake_versionStringCore___closed__5_once, _init_l_Lake_versionStringCore___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionStringCore(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_versionStringCore___closed__6, &l_Lake_versionStringCore___closed__6_once, _init_l_Lake_versionStringCore___closed__6);
return x_1;
}
}
static uint8_t _init_l_Lake_versionString___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = ((lean_object*)(l_Lake_versionString___closed__0));
x_2 = l_Lake_version_specialDesc;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_versionString___closed__2));
x_2 = l_Lake_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_version_specialDesc;
x_2 = lean_obj_once(&l_Lake_versionString___closed__3, &l_Lake_versionString___closed__3_once, _init_l_Lake_versionString___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_versionString(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l_Lake_versionString___closed__1, &l_Lake_versionString___closed__1_once, _init_l_Lake_versionString___closed__1);
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lake_versionString___closed__4, &l_Lake_versionString___closed__4_once, _init_l_Lake_versionString___closed__4);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_versionStringCore;
return x_3;
}
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_versionString;
x_2 = ((lean_object*)(l_Lake_uiVersionString___closed__0));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_uiVersionString___closed__2));
x_2 = lean_obj_once(&l_Lake_uiVersionString___closed__1, &l_Lake_uiVersionString___closed__1_once, _init_l_Lake_uiVersionString___closed__1);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionString;
x_2 = lean_obj_once(&l_Lake_uiVersionString___closed__3, &l_Lake_uiVersionString___closed__3_once, _init_l_Lake_uiVersionString___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_uiVersionString___closed__5));
x_2 = lean_obj_once(&l_Lake_uiVersionString___closed__4, &l_Lake_uiVersionString___closed__4_once, _init_l_Lake_uiVersionString___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_uiVersionString(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_uiVersionString___closed__6, &l_Lake_uiVersionString___closed__6_once, _init_l_Lake_uiVersionString___closed__6);
return x_1;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Version(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_version_major = _init_l_Lake_version_major();
lean_mark_persistent(l_Lake_version_major);
l_Lake_version_minor = _init_l_Lake_version_minor();
lean_mark_persistent(l_Lake_version_minor);
l_Lake_version_patch = _init_l_Lake_version_patch();
lean_mark_persistent(l_Lake_version_patch);
l_Lake_version_isRelease = _init_l_Lake_version_isRelease();
l_Lake_version_specialDesc = _init_l_Lake_version_specialDesc();
lean_mark_persistent(l_Lake_version_specialDesc);
l_Lake_versionStringCore = _init_l_Lake_versionStringCore();
lean_mark_persistent(l_Lake_versionStringCore);
l_Lake_versionString = _init_l_Lake_versionString();
lean_mark_persistent(l_Lake_versionString);
l_Lake_uiVersionString = _init_l_Lake_uiVersionString();
lean_mark_persistent(l_Lake_uiVersionString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

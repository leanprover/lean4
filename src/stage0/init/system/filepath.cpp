// Lean compiler output
// Module: init.system.filepath
// Imports: init.system.platform init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_String_revPosOf(obj*, uint32);
obj* l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1___boxed(obj*, obj*, obj*);
uint32 l_System_FilePath_pathSeparator___closed__1;
obj* l_List_lengthAux___main___rarg(obj*, obj*);
obj* l_System_FilePath_pathSeparators___closed__3;
obj* l_System_FilePath_normalizePathSeparators___closed__1;
extern uint8 l_System_Platform_isWindows;
obj* l_String_mapAux___main___at_System_FilePath_normalizePathSeparators___spec__2(obj*, obj*);
obj* l_System_FilePath_pathSeparators___closed__2;
uint32 l_System_FilePath_searchPathSeparator;
obj* l_System_FilePath_pathSeparators;
obj* l_System_FilePath_pathSeparators___closed__1;
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_System_FilePath_dirName(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint32 l_System_FilePath_searchPathSeparator___closed__1;
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_System_FilePath_dirName___closed__1;
uint32 l_System_FilePath_extSeparator;
uint8 l_System_FilePath_normalizePathSeparators___closed__2;
obj* l_System_FilePath_normalizePathSeparators(obj*);
uint32 l_System_FilePath_pathSeparator;
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
uint8 l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1(uint32, uint8, obj*);
namespace lean {
obj* string_utf8_set(obj*, obj*, uint32);
}
uint32 _init_l_System_FilePath_pathSeparator___closed__1() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32 x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32 x_3; 
x_3 = 92;
return x_3;
}
}
}
uint32 _init_l_System_FilePath_pathSeparator() {
_start:
{
uint32 x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
return x_1;
}
}
obj* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = 47;
x_2 = lean::box(0);
x_3 = lean::box_uint32(x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* _init_l_System_FilePath_pathSeparators___closed__2() {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = 92;
x_2 = l_System_FilePath_pathSeparators___closed__1;
x_3 = lean::box_uint32(x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* _init_l_System_FilePath_pathSeparators___closed__3() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__2;
return x_3;
}
}
}
obj* _init_l_System_FilePath_pathSeparators() {
_start:
{
obj* x_1; 
x_1 = l_System_FilePath_pathSeparators___closed__3;
return x_1;
}
}
uint32 _init_l_System_FilePath_searchPathSeparator___closed__1() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32 x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32 x_3; 
x_3 = 59;
return x_3;
}
}
}
uint32 _init_l_System_FilePath_searchPathSeparator() {
_start:
{
uint32 x_1; 
x_1 = l_System_FilePath_searchPathSeparator___closed__1;
return x_1;
}
}
uint32 _init_l_System_FilePath_extSeparator() {
_start:
{
uint32 x_1; 
x_1 = 46;
return x_1;
}
}
uint8 l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1(uint32 x_1, uint8 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
return x_2;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; uint32 x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1(x_1, x_2, x_5);
x_7 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_1 == x_7;
if (x_8 == 0)
{
return x_6;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
obj* l_String_mapAux___main___at_System_FilePath_normalizePathSeparators___spec__2(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; obj* x_6; uint8 x_7; 
x_4 = lean::string_utf8_get(x_2, x_1);
x_5 = 0;
x_6 = l_System_FilePath_pathSeparators;
x_7 = l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1(x_4, x_5, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::string_utf8_set(x_2, x_1, x_4);
x_9 = lean::string_utf8_next(x_8, x_1);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_8;
goto _start;
}
else
{
uint32 x_11; obj* x_12; obj* x_13; 
x_11 = l_System_FilePath_pathSeparator;
x_12 = lean::string_utf8_set(x_2, x_1, x_11);
x_13 = lean::string_utf8_next(x_12, x_1);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_12;
goto _start;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* _init_l_System_FilePath_normalizePathSeparators___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = lean::mk_nat_obj(0u);
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
uint8 _init_l_System_FilePath_normalizePathSeparators___closed__2() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_System_FilePath_normalizePathSeparators___closed__1;
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_dec_eq(x_1, x_2);
return x_3;
}
}
obj* l_System_FilePath_normalizePathSeparators(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_System_FilePath_normalizePathSeparators___closed__2;
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_String_mapAux___main___at_System_FilePath_normalizePathSeparators___spec__2(x_3, x_1);
return x_4;
}
else
{
return x_1;
}
}
}
obj* l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; uint8 x_5; uint8 x_6; obj* x_7; 
x_4 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_5 = lean::unbox(x_2);
lean::dec(x_2);
x_6 = l_List_foldr___main___at_System_FilePath_normalizePathSeparators___spec__1(x_4, x_5, x_3);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* _init_l_System_FilePath_dirName___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(".");
return x_1;
}
}
obj* l_System_FilePath_dirName(obj* x_1) {
_start:
{
obj* x_2; uint32 x_3; obj* x_4; 
x_2 = l_System_FilePath_normalizePathSeparators(x_1);
x_3 = l_System_FilePath_pathSeparator;
x_4 = l_String_revPosOf(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = l_System_FilePath_dirName___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::string_utf8_extract(x_2, x_7, x_6);
lean::dec(x_6);
lean::dec(x_2);
return x_8;
}
}
}
obj* initialize_init_system_platform(obj*);
obj* initialize_init_data_string_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_system_filepath(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_system_platform(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
l_System_FilePath_pathSeparator___closed__1 = _init_l_System_FilePath_pathSeparator___closed__1();
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean::mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators___closed__2 = _init_l_System_FilePath_pathSeparators___closed__2();
lean::mark_persistent(l_System_FilePath_pathSeparators___closed__2);
l_System_FilePath_pathSeparators___closed__3 = _init_l_System_FilePath_pathSeparators___closed__3();
lean::mark_persistent(l_System_FilePath_pathSeparators___closed__3);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean::mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_searchPathSeparator___closed__1 = _init_l_System_FilePath_searchPathSeparator___closed__1();
l_System_FilePath_searchPathSeparator = _init_l_System_FilePath_searchPathSeparator();
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_normalizePathSeparators___closed__1 = _init_l_System_FilePath_normalizePathSeparators___closed__1();
lean::mark_persistent(l_System_FilePath_normalizePathSeparators___closed__1);
l_System_FilePath_normalizePathSeparators___closed__2 = _init_l_System_FilePath_normalizePathSeparators___closed__2();
l_System_FilePath_dirName___closed__1 = _init_l_System_FilePath_dirName___closed__1();
lean::mark_persistent(l_System_FilePath_dirName___closed__1);
return w;
}

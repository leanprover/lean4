// Lean compiler output
// Module: Lake.Util.IO
// Imports: public import Init.System.IO
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
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs___boxed(lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
lean_object* lean_io_symlink_metadata(lean_object*);
uint8_t l_IO_FS_instBEqFileType_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object*);
lean_object* lean_io_read_dir(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_io_remove_dir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolvePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_resolvePath___closed__0 = (const lean_object*)&l_Lake_resolvePath___closed__0_value;
lean_object* lean_io_realpath(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_IO_FS_createDirAll(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_createParentDirs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_createParentDirs(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_file(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 11)
{
uint8_t x_5; 
lean_dec_ref(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_removeFileIfExists(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_array_uget(x_1, x_3);
x_16 = l_IO_FS_DirEntry_path(x_15);
x_17 = lean_io_symlink_metadata(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 16);
lean_dec(x_18);
x_20 = 0;
x_21 = l_IO_FS_instBEqFileType_beq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lake_removeFileIfExists(x_16);
lean_dec_ref(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_6 = x_14;
x_7 = lean_box(0);
goto block_11;
}
else
{
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = l_Lake_removeDirAllIfExists(x_16);
lean_dec_ref(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_6 = x_14;
x_7 = lean_box(0);
goto block_11;
}
else
{
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_16);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_25) == 11)
{
lean_free_object(x_17);
lean_dec_ref(x_25);
x_6 = x_14;
x_7 = lean_box(0);
goto block_11;
}
else
{
return x_17;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
if (lean_obj_tag(x_26) == 11)
{
lean_dec_ref(x_26);
x_6 = x_14;
x_7 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_read_dir(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_box(0);
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(x_4, x_6, x_7, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = lean_io_remove_dir(x_1);
if (lean_obj_tag(x_9) == 0)
{
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 11)
{
uint8_t x_11; 
lean_dec_ref(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
else
{
lean_dec(x_10);
return x_9;
}
}
}
else
{
return x_8;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_15) == 11)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
else
{
return x_3;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
if (lean_obj_tag(x_17) == 11)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_removeDirAllIfExists(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readBinFile(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_IO_FS_writeBinFile(x_2, x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_copyFile(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_System_FilePath_pathExists(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = ((lean_object*)(l_Lake_resolvePath___closed__0));
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_System_FilePath_normalize(x_4);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_3);
x_8 = ((lean_object*)(l_Lake_resolvePath___closed__0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_resolvePath(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_resolvePath(x_1);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec_ref(x_3);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_resolvePath_x3f(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

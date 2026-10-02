// Lean compiler output
// Module: Std.Time.Zoned.Database.TZdb
// Imports: public import Std.Time.Zoned.Database.Basic import Init.Data.String.TakeDrop
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_getenv(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static const lean_closure_object l_Std_Time_Database_TZdb_parseTZif___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_parseTZif___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZif___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZif(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unable to locate "};
static const lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = " in the local timezone database at '"};
static const lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1_value;
static const lean_string_object l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_idFromPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_idFromPath___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_idFromPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_idFromPath___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_localRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "cannot read the id of the path."};
static const lean_object* l_Std_Time_Database_TZdb_localRules___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_localRules___closed__0_value;
static lean_once_cell_t l_Std_Time_Database_TZdb_localRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.Database.TZdb.TZSpec.filePath"};
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0_value)}};
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2_value;
static lean_once_cell_t l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3;
static lean_once_cell_t l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4;
static const lean_string_object l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Time.Database.TZdb.TZSpec.zoneId"};
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5_value)}};
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Database_TZdb_instReprTZSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_TZdb_instReprTZSpec = (const lean_object*)&l_Std_Time_Database_TZdb_instReprTZSpec___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Database_TZdb_instBEqTZSpec_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec = (const lean_object*)&l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_parseTZValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Time_Database_TZdb_parseTZValue___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZValue___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZValue(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "TZ"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "TZ='"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__1_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "': path '"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__2_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "' not found in any zoneinfo directory"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__3 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__3_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "': timezone not found in any zoneinfo directory"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__4 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "/etc/localtime"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__5 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/usr/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__1_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/etc/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__2_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "/usr/share/lib/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__3 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__3_value;
static const lean_array_object l_Std_Time_Database_TZdb_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_Database_TZdb_default___closed__0_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__1_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__2_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__3_value)}};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__4 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_TZdb_default = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__4_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TZDIR"};
static const lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_getZoneRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot find "};
static const lean_object* l_Std_Time_Database_TZdb_getZoneRules___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_getZoneRules___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_getZoneRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " in the local timezone database"};
static const lean_object* l_Std_Time_Database_TZdb_getZoneRules___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_getZoneRules___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Database_TZdb_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_TZdb_getZoneRules___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_inst___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___closed__0_value;
static const lean_closure_object l_Std_Time_Database_TZdb_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_TZdb_getLocalZoneRules___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_inst___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___closed__1_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Database_TZdb_inst___closed__0_value),((lean_object*)&l_Std_Time_Database_TZdb_inst___closed__1_value)}};
static const lean_object* l_Std_Time_Database_TZdb_inst___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_TZdb_inst = (const lean_object*)&l_Std_Time_Database_TZdb_inst___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZif(lean_object* v_bin_2_, lean_object* v_id_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZif___closed__0));
v___x_5_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_4_, v_bin_2_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_13_; 
lean_dec_ref(v_id_3_);
v_a_6_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_13_ == 0)
{
v___x_8_ = v___x_5_;
v_isShared_9_ = v_isSharedCheck_13_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_a_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_13_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_11_; 
if (v_isShared_9_ == 0)
{
v___x_11_ = v___x_8_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_a_6_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
else
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_5_, 1);
v___x_15_ = l_Std_Time_TimeZone_convertTZif(v_a_14_, v_id_3_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(lean_object* v_e_16_){
_start:
{
if (lean_obj_tag(v_e_16_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_26_; 
v_a_18_ = lean_ctor_get(v_e_16_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v_e_16_);
if (v_isSharedCheck_26_ == 0)
{
v___x_20_ = v_e_16_;
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v_e_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_mk_io_user_error(v_a_18_);
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 1);
lean_ctor_set(v___x_20_, 0, v___x_22_);
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
v_a_27_ = lean_ctor_get(v_e_16_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v_e_16_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v_e_16_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v_e_16_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 0);
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg___boxed(lean_object* v_e_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(lean_object* v_00_u03b1_38_, lean_object* v_e_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___boxed(lean_object* v_00_u03b1_42_, lean_object* v_e_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(v_00_u03b1_42_, v_e_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object* v_path_49_, lean_object* v_id_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_IO_FS_readBinFile(v_path_49_);
if (lean_obj_tag(v___x_52_) == 0)
{
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_52_, 1);
v___x_54_ = l_Std_Time_Database_TZdb_parseTZif(v_a_53_, v_id_50_);
v___x_55_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec_ref(v_id_50_);
v_a_56_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_52_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 1);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
else
{
lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_79_);
v___x_65_ = v___x_52_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_dec(v___x_52_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_67_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0));
v___x_68_ = lean_string_append(v___x_67_, v_id_50_);
lean_dec_ref(v_id_50_);
v___x_69_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1));
v___x_70_ = lean_string_append(v___x_68_, v___x_69_);
v___x_71_ = lean_string_append(v___x_70_, v_path_49_);
v___x_72_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2));
v___x_73_ = lean_string_append(v___x_71_, v___x_72_);
v___x_74_ = lean_mk_io_user_error(v___x_73_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_74_);
v___x_76_ = v___x_65_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object* v_path_80_, lean_object* v_id_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_80_, v_id_81_);
lean_dec_ref(v_path_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object* v_path_86_){
_start:
{
lean_object* v___x_87_; lean_object* v_res_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_87_ = l_System_FilePath_components(v_path_86_);
v_res_88_ = lean_array_mk(v___x_87_);
v___x_89_ = lean_array_get_size(v_res_88_);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_sub(v___x_89_, v___x_90_);
v___x_92_ = lean_nat_dec_lt(v___x_91_, v___x_89_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec(v___x_91_);
lean_dec_ref(v_res_88_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(2u);
v___x_95_ = lean_nat_sub(v___x_89_, v___x_94_);
v___x_96_ = lean_nat_dec_lt(v___x_95_, v___x_89_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec(v___x_95_);
lean_dec(v___x_91_);
lean_dec_ref(v_res_88_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_98_ = lean_array_fget(v_res_88_, v___x_91_);
lean_dec(v___x_91_);
v___x_99_ = lean_array_fget(v_res_88_, v___x_95_);
lean_dec(v___x_95_);
lean_dec_ref(v_res_88_);
v___x_100_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__0));
v___x_101_ = lean_string_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_str_106_; lean_object* v_startInclusive_107_; lean_object* v_endExclusive_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_126_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_string_utf8_byte_size(v___x_99_);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_99_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
v___x_105_ = l_String_Slice_trimAscii(v___x_104_);
v_str_106_ = lean_ctor_get(v___x_105_, 0);
v_startInclusive_107_ = lean_ctor_get(v___x_105_, 1);
v_endExclusive_108_ = lean_ctor_get(v___x_105_, 2);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_126_ == 0)
{
v___x_110_ = v___x_105_;
v_isShared_111_ = v_isSharedCheck_126_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_endExclusive_108_);
lean_inc(v_startInclusive_107_);
lean_inc(v_str_106_);
lean_dec(v___x_105_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_126_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_string_utf8_byte_size(v___x_98_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 2, v___x_112_);
lean_ctor_set(v___x_110_, 1, v___x_102_);
lean_ctor_set(v___x_110_, 0, v___x_98_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v___x_112_);
v___x_114_ = v_reuseFailAlloc_125_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v_str_116_; lean_object* v_startInclusive_117_; lean_object* v_endExclusive_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_115_ = l_String_Slice_trimAscii(v___x_114_);
v_str_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_str_116_);
v_startInclusive_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc(v_startInclusive_117_);
v_endExclusive_118_ = lean_ctor_get(v___x_115_, 2);
lean_inc(v_endExclusive_118_);
lean_dec_ref(v___x_115_);
v___x_119_ = lean_string_utf8_extract_fast(v_str_106_, v_startInclusive_107_, v_endExclusive_108_);
lean_dec(v_endExclusive_108_);
lean_dec(v_startInclusive_107_);
lean_dec_ref(v_str_106_);
v___x_120_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_121_ = lean_string_append(v___x_119_, v___x_120_);
v___x_122_ = lean_string_utf8_extract_fast(v_str_116_, v_startInclusive_117_, v_endExclusive_118_);
lean_dec(v_endExclusive_118_);
lean_dec(v_startInclusive_117_);
lean_dec_ref(v_str_116_);
v___x_123_ = lean_string_append(v___x_121_, v___x_122_);
lean_dec_ref(v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_str_131_; lean_object* v_startInclusive_132_; lean_object* v_endExclusive_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v___x_99_);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_string_utf8_byte_size(v___x_98_);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_98_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
v___x_130_ = l_String_Slice_trimAscii(v___x_129_);
v_str_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc_ref(v_str_131_);
v_startInclusive_132_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_startInclusive_132_);
v_endExclusive_133_ = lean_ctor_get(v___x_130_, 2);
lean_inc(v_endExclusive_133_);
lean_dec_ref(v___x_130_);
v___x_134_ = lean_string_utf8_extract_fast(v_str_131_, v_startInclusive_132_, v_endExclusive_133_);
lean_dec(v_endExclusive_133_);
lean_dec(v_startInclusive_132_);
lean_dec_ref(v_str_131_);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__1(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Std_Time_Database_TZdb_localRules___closed__0));
v___x_138_ = lean_mk_io_user_error(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object* v_path_139_){
_start:
{
lean_object* v___x_141_; 
lean_inc_ref(v_path_139_);
v___x_141_ = lean_io_realpath(v_path_139_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_153_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_153_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_153_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_153_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_Time_Database_TZdb_idFromPath(v_a_142_);
if (lean_obj_tag(v___x_146_) == 1)
{
lean_object* v_val_147_; lean_object* v___x_148_; 
lean_del_object(v___x_144_);
v_val_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v___x_146_, 1);
v___x_148_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_139_, v_val_147_);
lean_dec_ref(v_path_139_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_151_; 
lean_dec(v___x_146_);
lean_dec_ref(v_path_139_);
v___x_149_ = lean_obj_once(&l_Std_Time_Database_TZdb_localRules___closed__1, &l_Std_Time_Database_TZdb_localRules___closed__1_once, _init_l_Std_Time_Database_TZdb_localRules___closed__1);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 1);
lean_ctor_set(v___x_144_, 0, v___x_149_);
v___x_151_ = v___x_144_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_path_139_);
v_a_154_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_141_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_141_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___boxed(lean_object* v_path_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Time_Database_TZdb_localRules(v_path_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object* v_path_165_, lean_object* v_id_166_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc_ref(v_id_166_);
v___x_168_ = l_System_FilePath_join(v_path_165_, v_id_166_);
v___x_169_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v___x_168_, v_id_166_);
lean_dec_ref(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(lean_object* v_path_170_, lean_object* v_id_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_path_170_, v_id_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx(lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(0u);
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(1u);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___boxed(lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_Database_TZdb_TZSpec_ctorIdx(v_x_177_);
lean_dec_ref(v_x_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(lean_object* v_t_179_, lean_object* v_k_180_){
_start:
{
lean_object* v_p_181_; lean_object* v___x_182_; 
v_p_181_ = lean_ctor_get(v_t_179_, 0);
lean_inc_ref(v_p_181_);
lean_dec_ref(v_t_179_);
v___x_182_ = lean_apply_1(v_k_180_, v_p_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim(lean_object* v_motive_183_, lean_object* v_ctorIdx_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_k_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_185_, v_k_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___boxed(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim(v_motive_189_, v_ctorIdx_190_, v_t_191_, v_h_192_, v_k_193_);
lean_dec(v_ctorIdx_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim___redArg(lean_object* v_t_195_, lean_object* v_filePath_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_195_, v_filePath_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_filePath_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_199_, v_filePath_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim___redArg(lean_object* v_t_203_, lean_object* v_zoneId_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_203_, v_zoneId_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_zoneId_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_207_, v_zoneId_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(2u);
v___x_218_ = lean_nat_to_int(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr(lean_object* v_x_227_, lean_object* v_prec_228_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v_p_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_249_; 
v_p_229_ = lean_ctor_get(v_x_227_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_249_ == 0)
{
v___x_231_ = v_x_227_;
v_isShared_232_ = v_isSharedCheck_249_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_p_229_);
lean_dec(v_x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_249_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___y_234_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1024u);
v___x_246_ = lean_nat_dec_le(v___x_245_, v_prec_228_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_234_ = v___x_247_;
goto v___jp_233_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_234_ = v___x_248_;
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_235_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2));
v___x_236_ = l_String_quote(v_p_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 3);
lean_ctor_set(v___x_231_, 0, v___x_236_);
v___x_238_ = v___x_231_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_244_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_235_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_inc(v___y_234_);
v___x_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_240_, 0, v___y_234_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v_prec_228_);
return v___x_243_;
}
}
}
}
else
{
lean_object* v_id_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_270_; 
v_id_250_ = lean_ctor_get(v_x_227_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_270_ == 0)
{
v___x_252_ = v_x_227_;
v_isShared_253_ = v_isSharedCheck_270_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_id_250_);
lean_dec(v_x_227_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_270_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___y_255_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1024u);
v___x_267_ = lean_nat_dec_le(v___x_266_, v_prec_228_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_255_ = v___x_268_;
goto v___jp_254_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_255_ = v___x_269_;
goto v___jp_254_;
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7));
v___x_257_ = l_String_quote(v_id_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 3);
lean_ctor_set(v___x_252_, 0, v___x_257_);
v___x_259_ = v___x_252_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_265_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_inc(v___y_255_);
v___x_261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_261_, 0, v___y_255_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = 0;
v___x_263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*1, v___x_262_);
v___x_264_ = l_Repr_addAppParen(v___x_263_, v_prec_228_);
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed(lean_object* v_x_271_, lean_object* v_prec_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr(v_x_271_, v_prec_272_);
lean_dec(v_prec_272_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Database_TZdb_instBEqTZSpec_beq(lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v_p_278_; lean_object* v_p_279_; uint8_t v___x_280_; 
v_p_278_ = lean_ctor_get(v_x_276_, 0);
v_p_279_ = lean_ctor_get(v_x_277_, 0);
v___x_280_ = lean_string_dec_eq(v_p_278_, v_p_279_);
return v___x_280_;
}
else
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
else
{
if (lean_obj_tag(v_x_277_) == 1)
{
lean_object* v_id_282_; lean_object* v_id_283_; uint8_t v___x_284_; 
v_id_282_ = lean_ctor_get(v_x_276_, 0);
v_id_283_ = lean_ctor_get(v_x_277_, 0);
v___x_284_ = lean_string_dec_eq(v_id_282_, v_id_283_);
return v___x_284_;
}
else
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_Time_Database_TZdb_instBEqTZSpec_beq(v_x_286_, v_x_287_);
lean_dec_ref(v_x_287_);
lean_dec_ref(v_x_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZValue(lean_object* v_tz_293_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_string_utf8_byte_size(v_tz_293_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_dec_le(v___x_302_, v___x_301_);
if (v___x_303_ == 0)
{
goto v___jp_294_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_string_memcmp(v_tz_293_, v___x_304_, v___x_305_, v___x_305_, v___x_302_);
if (v___x_306_ == 0)
{
goto v___jp_294_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_p_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
lean_inc_ref(v_tz_293_);
v___x_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_307_, 0, v_tz_293_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
lean_ctor_set(v___x_307_, 2, v___x_301_);
v___x_308_ = l_String_Slice_Pos_nextn(v___x_307_, v___x_305_, v___x_302_);
lean_dec_ref_known(v___x_307_, 3);
v___x_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_309_, 0, v_tz_293_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_ctor_set(v___x_309_, 2, v___x_301_);
v_p_310_ = l_String_Slice_toString(v___x_309_);
lean_dec_ref_known(v___x_309_, 3);
v___x_311_ = lean_string_utf8_byte_size(v_p_310_);
v___x_312_ = lean_nat_dec_eq(v___x_311_, v___x_305_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v_p_310_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
lean_dec_ref(v_p_310_);
v___x_315_ = lean_box(0);
return v___x_315_;
}
}
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_string_utf8_byte_size(v_tz_293_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_nat_dec_eq(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_tz_293_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v_tz_293_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object* v_rel_319_, lean_object* v_as_320_, size_t v_sz_321_, size_t v_i_322_, lean_object* v_b_323_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_322_, v_sz_321_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v_rel_319_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_b_323_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_a_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
lean_dec_ref(v_b_323_);
v___x_327_ = lean_box(0);
v___x_328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_a_329_ = lean_array_uget_borrowed(v_as_320_, v_i_322_);
lean_inc_ref(v_rel_319_);
lean_inc(v_a_329_);
v___x_330_ = l_System_FilePath_join(v_a_329_, v_rel_319_);
v___x_331_ = l_System_FilePath_pathExists(v___x_330_);
if (v___x_331_ == 0)
{
size_t v___x_332_; size_t v___x_333_; 
lean_dec_ref(v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_322_, v___x_332_);
v_i_322_ = v___x_333_;
v_b_323_ = v___x_328_;
goto _start;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_rel_319_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_330_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_327_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object* v_rel_339_, lean_object* v_as_340_, lean_object* v_sz_341_, lean_object* v_i_342_, lean_object* v_b_343_, lean_object* v___y_344_){
_start:
{
size_t v_sz_boxed_345_; size_t v_i_boxed_346_; lean_object* v_res_347_; 
v_sz_boxed_345_ = lean_unbox_usize(v_sz_341_);
lean_dec(v_sz_341_);
v_i_boxed_346_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_339_, v_as_340_, v_sz_boxed_345_, v_i_boxed_346_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object* v_searchPaths_348_, lean_object* v_rel_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; size_t v_sz_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_351_ = lean_box(0);
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_sz_353_ = lean_array_size(v_searchPaths_348_);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_349_, v_searchPaths_348_, v_sz_353_, v___x_354_, v___x_352_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_368_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_368_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_368_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_368_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_fst_360_; 
v_fst_360_ = lean_ctor_get(v_a_356_, 0);
lean_inc(v_fst_360_);
lean_dec(v_a_356_);
if (lean_obj_tag(v_fst_360_) == 0)
{
lean_object* v___x_362_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_351_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_351_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
else
{
lean_object* v_val_364_; lean_object* v___x_366_; 
v_val_364_ = lean_ctor_get(v_fst_360_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_fst_360_, 1);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_val_364_);
v___x_366_ = v___x_358_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_val_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
v_a_369_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_355_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_355_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object* v_searchPaths_377_, lean_object* v_rel_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_377_, v_rel_378_);
lean_dec_ref(v_searchPaths_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object* v_zonesPaths_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0));
v___x_390_ = lean_io_getenv(v___x_389_);
if (lean_obj_tag(v___x_390_) == 1)
{
lean_object* v_val_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_472_; 
v_val_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_472_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_472_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_val_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_472_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; 
lean_inc(v_val_391_);
v___x_395_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_391_);
if (lean_obj_tag(v___x_395_) == 1)
{
lean_object* v_val_396_; 
lean_del_object(v___x_393_);
v_val_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_395_, 1);
if (lean_obj_tag(v_val_396_) == 0)
{
lean_object* v_p_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_440_; 
v_p_397_ = lean_ctor_get(v_val_396_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_val_396_);
if (v_isSharedCheck_440_ == 0)
{
v___x_399_ = v_val_396_;
v_isShared_400_ = v_isSharedCheck_440_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_p_397_);
lean_dec(v_val_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_440_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_string_utf8_byte_size(v_p_397_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_dec_le(v___x_432_, v___x_431_);
if (v___x_433_ == 0)
{
lean_del_object(v___x_399_);
goto v___jp_401_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_434_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_string_memcmp(v_p_397_, v___x_434_, v___x_435_, v___x_435_, v___x_432_);
if (v___x_436_ == 0)
{
lean_del_object(v___x_399_);
goto v___jp_401_;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_val_391_);
if (v_isShared_400_ == 0)
{
v___x_438_ = v___x_399_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_p_397_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
v___jp_401_:
{
lean_object* v___x_402_; 
lean_inc_ref(v_p_397_);
v___x_402_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_387_, v_p_397_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_422_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_422_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_422_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_422_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
if (lean_obj_tag(v_a_403_) == 1)
{
lean_object* v_val_407_; lean_object* v___x_409_; 
lean_dec_ref(v_p_397_);
lean_dec(v_val_391_);
v_val_407_ = lean_ctor_get(v_a_403_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v_a_403_, 1);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_val_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_val_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_a_403_);
v___x_411_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_412_ = lean_string_append(v___x_411_, v_val_391_);
lean_dec(v_val_391_);
v___x_413_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2));
v___x_414_ = lean_string_append(v___x_412_, v___x_413_);
v___x_415_ = lean_string_append(v___x_414_, v_p_397_);
lean_dec_ref(v_p_397_);
v___x_416_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = lean_mk_io_user_error(v___x_417_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_418_);
v___x_420_ = v___x_405_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_p_397_);
lean_dec(v_val_391_);
v_a_423_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_402_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_402_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
else
{
lean_object* v_id_441_; lean_object* v___x_442_; 
v_id_441_ = lean_ctor_get(v_val_396_, 0);
lean_inc_ref(v_id_441_);
lean_dec_ref_known(v_val_396_, 1);
v___x_442_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_387_, v_id_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_459_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_459_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_459_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_459_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_449_; 
lean_dec(v_val_391_);
v_val_447_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_443_, 1);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_val_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_val_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec(v_a_443_);
v___x_451_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_452_ = lean_string_append(v___x_451_, v_val_391_);
lean_dec(v_val_391_);
v___x_453_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__4));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = lean_mk_io_user_error(v___x_454_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
lean_ctor_set(v___x_445_, 0, v___x_455_);
v___x_457_ = v___x_445_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_val_391_);
v_a_460_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_442_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_442_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec(v___x_395_);
lean_dec(v_val_391_);
v___x_468_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 0);
lean_ctor_set(v___x_393_, 0, v___x_468_);
v___x_470_ = v___x_393_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v___x_390_);
v___x_473_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object* v_zonesPaths_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_475_);
lean_dec_ref(v_zonesPaths_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object* v_db_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0));
v___x_498_ = lean_io_getenv(v___x_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_db_495_);
return v___x_499_;
}
else
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_520_; 
v_val_500_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_520_ == 0)
{
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_520_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_520_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1));
v___x_505_ = lean_string_dec_eq(v_val_500_, v___x_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
v___x_506_ = l_System_FilePath_pathExists(v_val_500_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_val_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
lean_ctor_set(v___x_502_, 0, v_db_495_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_db_495_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_mk_empty_array_with_capacity(v___x_510_);
v___x_512_ = lean_array_push(v___x_511_, v_val_500_);
v___x_513_ = l_Array_append___redArg(v___x_512_, v_db_495_);
lean_dec_ref(v_db_495_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
lean_ctor_set(v___x_502_, 0, v___x_513_);
v___x_515_ = v___x_502_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_val_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
lean_ctor_set(v___x_502_, 0, v_db_495_);
v___x_518_ = v___x_502_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_db_495_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object* v_db_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object* v_db_524_){
_start:
{
lean_object* v___x_526_; lean_object* v_a_527_; lean_object* v___x_528_; 
v___x_526_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_524_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_527_);
lean_dec(v_a_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = l_Std_Time_Database_TZdb_localRules(v_a_529_);
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_528_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_528_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object* v_db_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object* v_id_545_, lean_object* v_as_546_, size_t v_sz_547_, size_t v_i_548_, lean_object* v_b_549_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = lean_usize_dec_lt(v_i_548_, v_sz_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec_ref(v_id_545_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_b_549_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
lean_dec_ref(v_b_549_);
v___x_553_ = lean_box(0);
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_a_555_ = lean_array_uget_borrowed(v_as_546_, v_i_548_);
lean_inc_ref(v_id_545_);
lean_inc(v_a_555_);
v___x_556_ = l_System_FilePath_join(v_a_555_, v_id_545_);
v___x_557_ = l_System_FilePath_pathExists(v___x_556_);
lean_dec_ref(v___x_556_);
if (v___x_557_ == 0)
{
size_t v___x_558_; size_t v___x_559_; 
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_548_, v___x_558_);
v_i_548_ = v___x_559_;
v_b_549_ = v___x_554_;
goto _start;
}
else
{
lean_object* v___x_561_; 
lean_inc(v_a_555_);
v___x_561_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_555_, v_id_545_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_571_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_a_562_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_553_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_a_572_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_561_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_561_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object* v_id_580_, lean_object* v_as_581_, lean_object* v_sz_582_, lean_object* v_i_583_, lean_object* v_b_584_, lean_object* v___y_585_){
_start:
{
size_t v_sz_boxed_586_; size_t v_i_boxed_587_; lean_object* v_res_588_; 
v_sz_boxed_586_ = lean_unbox_usize(v_sz_582_);
lean_dec(v_sz_582_);
v_i_boxed_587_ = lean_unbox_usize(v_i_583_);
lean_dec(v_i_583_);
v_res_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_580_, v_as_581_, v_sz_boxed_586_, v_i_boxed_587_, v_b_584_);
lean_dec_ref(v_as_581_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object* v_db_591_, lean_object* v_id_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_596_; size_t v_sz_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_594_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_591_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref(v___x_594_);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_sz_597_ = lean_array_size(v_a_595_);
v___x_598_ = ((size_t)0ULL);
lean_inc_ref(v_id_592_);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_592_, v_a_595_, v_sz_597_, v___x_598_, v___x_596_);
lean_dec(v_a_595_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_617_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_617_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_617_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_617_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_fst_604_; 
v_fst_604_ = lean_ctor_get(v_a_600_, 0);
lean_inc(v_fst_604_);
lean_dec(v_a_600_);
if (lean_obj_tag(v_fst_604_) == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_605_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__0));
v___x_606_ = lean_string_append(v___x_605_, v_id_592_);
lean_dec_ref(v_id_592_);
v___x_607_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__1));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = lean_mk_io_user_error(v___x_608_);
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 1);
lean_ctor_set(v___x_602_, 0, v___x_609_);
v___x_611_ = v___x_602_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; 
lean_dec_ref(v_id_592_);
v_val_613_ = lean_ctor_get(v_fst_604_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v_fst_604_, 1);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_val_613_);
v___x_615_ = v___x_602_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_val_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_id_592_);
v_a_618_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_599_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_599_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object* v_db_626_, lean_object* v_id_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_626_, v_id_627_);
return v_res_629_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_TZdb(builtin);
}
#ifdef __cplusplus
}
#endif

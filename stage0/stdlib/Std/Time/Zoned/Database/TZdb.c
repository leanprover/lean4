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
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_Database_TZdb_parseTZValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_parseTZValue___closed__1;
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
static lean_once_cell_t l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__4;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "': timezone not found in any zoneinfo directory"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__5 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__5_value;
static const lean_string_object l_Std_Time_Database_TZdb_resolveLocalPath___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "/etc/localtime"};
static const lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___closed__6 = (const lean_object*)&l_Std_Time_Database_TZdb_resolveLocalPath___closed__6_value;
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
v___x_119_ = lean_string_utf8_extract(v_str_106_, v_startInclusive_107_, v_endExclusive_108_);
lean_dec(v_endExclusive_108_);
lean_dec(v_startInclusive_107_);
lean_dec_ref(v_str_106_);
v___x_120_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_121_ = lean_string_append(v___x_119_, v___x_120_);
v___x_122_ = lean_string_utf8_extract(v_str_116_, v_startInclusive_117_, v_endExclusive_118_);
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
v___x_134_ = lean_string_utf8_extract(v_str_131_, v_startInclusive_132_, v_endExclusive_133_);
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
static lean_object* _init_l_Std_Time_Database_TZdb_parseTZValue___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_294_ = lean_string_utf8_byte_size(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZValue(lean_object* v_tz_295_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_305_ = lean_string_utf8_byte_size(v_tz_295_);
v___x_306_ = lean_obj_once(&l_Std_Time_Database_TZdb_parseTZValue___closed__1, &l_Std_Time_Database_TZdb_parseTZValue___closed__1_once, _init_l_Std_Time_Database_TZdb_parseTZValue___closed__1);
v___x_307_ = lean_nat_dec_le(v___x_306_, v___x_305_);
if (v___x_307_ == 0)
{
goto v___jp_296_;
}
else
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_string_memcmp(v_tz_295_, v___x_304_, v___x_308_, v___x_308_, v___x_306_);
if (v___x_309_ == 0)
{
goto v___jp_296_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_p_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_310_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_tz_295_);
v___x_311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_311_, 0, v_tz_295_);
lean_ctor_set(v___x_311_, 1, v___x_308_);
lean_ctor_set(v___x_311_, 2, v___x_305_);
v___x_312_ = l_String_Slice_Pos_nextn(v___x_311_, v___x_308_, v___x_310_);
lean_dec_ref_known(v___x_311_, 3);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v_tz_295_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
lean_ctor_set(v___x_313_, 2, v___x_305_);
v_p_314_ = l_String_Slice_toString(v___x_313_);
lean_dec_ref_known(v___x_313_, 3);
v___x_315_ = lean_string_utf8_byte_size(v_p_314_);
v___x_316_ = lean_nat_dec_eq(v___x_315_, v___x_308_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_p_314_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
lean_dec_ref(v_p_314_);
v___x_319_ = lean_box(0);
return v___x_319_;
}
}
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_297_ = lean_string_utf8_byte_size(v_tz_295_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v___x_297_, v___x_298_);
v___x_300_ = lean_bool_not(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec_ref(v_tz_295_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v_tz_295_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object* v_rel_323_, lean_object* v_as_324_, size_t v_sz_325_, size_t v_i_326_, lean_object* v_b_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v_rel_323_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_327_);
return v___x_330_;
}
else
{
lean_object* v_a_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
lean_dec_ref(v_b_327_);
v_a_331_ = lean_array_uget_borrowed(v_as_324_, v_i_326_);
lean_inc_ref(v_rel_323_);
lean_inc(v_a_331_);
v___x_332_ = l_System_FilePath_join(v_a_331_, v_rel_323_);
v___x_333_ = l_System_FilePath_pathExists(v___x_332_);
v___x_334_ = lean_box(0);
if (v___x_333_ == 0)
{
lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; 
lean_dec_ref(v___x_332_);
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_326_, v___x_336_);
v_i_326_ = v___x_337_;
v_b_327_ = v___x_335_;
goto _start;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref(v_rel_323_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_332_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_334_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object* v_rel_343_, lean_object* v_as_344_, lean_object* v_sz_345_, lean_object* v_i_346_, lean_object* v_b_347_, lean_object* v___y_348_){
_start:
{
size_t v_sz_boxed_349_; size_t v_i_boxed_350_; lean_object* v_res_351_; 
v_sz_boxed_349_ = lean_unbox_usize(v_sz_345_);
lean_dec(v_sz_345_);
v_i_boxed_350_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_343_, v_as_344_, v_sz_boxed_349_, v_i_boxed_350_, v_b_347_);
lean_dec_ref(v_as_344_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object* v_searchPaths_352_, lean_object* v_rel_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; size_t v_sz_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_355_ = lean_box(0);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_sz_357_ = lean_array_size(v_searchPaths_352_);
v___x_358_ = ((size_t)0ULL);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_353_, v_searchPaths_352_, v_sz_357_, v___x_358_, v___x_356_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_372_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_372_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_fst_364_; 
v_fst_364_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_fst_364_);
lean_dec(v_a_360_);
if (lean_obj_tag(v_fst_364_) == 0)
{
lean_object* v___x_366_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_355_);
v___x_366_ = v___x_362_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_355_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
else
{
lean_object* v_val_368_; lean_object* v___x_370_; 
v_val_368_ = lean_ctor_get(v_fst_364_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v_fst_364_, 1);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_val_368_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_val_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_359_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_359_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object* v_searchPaths_381_, lean_object* v_rel_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_381_, v_rel_382_);
lean_dec_ref(v_searchPaths_381_);
return v_res_384_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_resolveLocalPath___closed__4(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_390_ = lean_string_utf8_byte_size(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object* v_zonesPaths_393_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0));
v___x_396_ = lean_io_getenv(v___x_395_);
if (lean_obj_tag(v___x_396_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_478_; 
v_val_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_478_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_478_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_val_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_478_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; 
lean_inc(v_val_397_);
v___x_401_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_397_);
if (lean_obj_tag(v___x_401_) == 1)
{
lean_object* v_val_402_; 
lean_del_object(v___x_399_);
v_val_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_401_, 1);
if (lean_obj_tag(v_val_402_) == 0)
{
lean_object* v_p_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_446_; 
v_p_403_ = lean_ctor_get(v_val_402_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_val_402_);
if (v_isSharedCheck_446_ == 0)
{
v___x_405_ = v_val_402_;
v_isShared_406_ = v_isSharedCheck_446_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_p_403_);
lean_dec(v_val_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_446_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_437_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_438_ = lean_string_utf8_byte_size(v_p_403_);
v___x_439_ = lean_obj_once(&l_Std_Time_Database_TZdb_resolveLocalPath___closed__4, &l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_once, _init_l_Std_Time_Database_TZdb_resolveLocalPath___closed__4);
v___x_440_ = lean_nat_dec_le(v___x_439_, v___x_438_);
if (v___x_440_ == 0)
{
lean_del_object(v___x_405_);
goto v___jp_407_;
}
else
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_string_memcmp(v_p_403_, v___x_437_, v___x_441_, v___x_441_, v___x_439_);
if (v___x_442_ == 0)
{
lean_del_object(v___x_405_);
goto v___jp_407_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v_val_397_);
if (v_isShared_406_ == 0)
{
v___x_444_ = v___x_405_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_p_403_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
v___jp_407_:
{
lean_object* v___x_408_; 
lean_inc_ref(v_p_403_);
v___x_408_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_393_, v_p_403_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_428_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_428_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_428_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_428_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
if (lean_obj_tag(v_a_409_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_415_; 
lean_dec_ref(v_p_403_);
lean_dec(v_val_397_);
v_val_413_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v_a_409_, 1);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v_val_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_val_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec(v_a_409_);
v___x_417_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_418_ = lean_string_append(v___x_417_, v_val_397_);
lean_dec(v_val_397_);
v___x_419_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2));
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
v___x_421_ = lean_string_append(v___x_420_, v_p_403_);
lean_dec_ref(v_p_403_);
v___x_422_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3));
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
v___x_424_ = lean_mk_io_user_error(v___x_423_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 0, v___x_424_);
v___x_426_ = v___x_411_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_p_403_);
lean_dec(v_val_397_);
v_a_429_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_408_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_408_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
else
{
lean_object* v_id_447_; lean_object* v___x_448_; 
v_id_447_ = lean_ctor_get(v_val_402_, 0);
lean_inc_ref(v_id_447_);
lean_dec_ref_known(v_val_402_, 1);
v___x_448_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_393_, v_id_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_465_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
if (lean_obj_tag(v_a_449_) == 1)
{
lean_object* v_val_453_; lean_object* v___x_455_; 
lean_dec(v_val_397_);
v_val_453_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v_a_449_, 1);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_val_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_val_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec(v_a_449_);
v___x_457_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_458_ = lean_string_append(v___x_457_, v_val_397_);
lean_dec(v_val_397_);
v___x_459_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
v___x_460_ = lean_string_append(v___x_458_, v___x_459_);
v___x_461_ = lean_mk_io_user_error(v___x_460_);
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
lean_ctor_set(v___x_451_, 0, v___x_461_);
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_val_397_);
v_a_466_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_448_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_448_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_476_; 
lean_dec(v___x_401_);
lean_dec(v_val_397_);
v___x_474_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__6));
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v___x_474_);
v___x_476_ = v___x_399_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v___x_396_);
v___x_479_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__6));
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object* v_zonesPaths_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_481_);
lean_dec_ref(v_zonesPaths_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object* v_db_501_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0));
v___x_504_ = lean_io_getenv(v___x_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_505_; 
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v_db_501_);
return v___x_505_;
}
else
{
lean_object* v_val_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_526_; 
v_val_506_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_526_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_526_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_val_506_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_526_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1));
v___x_511_ = lean_string_dec_eq(v_val_506_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = l_System_FilePath_pathExists(v_val_506_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_val_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 0, v_db_501_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_db_501_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_mk_empty_array_with_capacity(v___x_516_);
v___x_518_ = lean_array_push(v___x_517_, v_val_506_);
v___x_519_ = l_Array_append___redArg(v___x_518_, v_db_501_);
lean_dec_ref(v_db_501_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 0, v___x_519_);
v___x_521_ = v___x_508_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v___x_524_; 
lean_dec(v_val_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 0, v_db_501_);
v___x_524_ = v___x_508_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_db_501_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object* v_db_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object* v_db_530_){
_start:
{
lean_object* v___x_532_; lean_object* v_a_533_; lean_object* v___x_534_; 
v___x_532_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_530_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_533_);
lean_dec(v_a_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = l_Std_Time_Database_TZdb_localRules(v_a_535_);
return v___x_536_;
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_534_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object* v_db_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object* v_id_551_, lean_object* v_as_552_, size_t v_sz_553_, size_t v_i_554_, lean_object* v_b_555_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_554_, v_sz_553_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec_ref(v_id_551_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_b_555_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v_b_555_);
v_a_559_ = lean_array_uget_borrowed(v_as_552_, v_i_554_);
lean_inc_ref(v_id_551_);
lean_inc(v_a_559_);
v___x_560_ = l_System_FilePath_join(v_a_559_, v_id_551_);
v___x_561_ = l_System_FilePath_pathExists(v___x_560_);
lean_dec_ref(v___x_560_);
v___x_562_ = lean_box(0);
if (v___x_561_ == 0)
{
lean_object* v___x_563_; size_t v___x_564_; size_t v___x_565_; 
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_554_, v___x_564_);
v_i_554_ = v___x_565_;
v_b_555_ = v___x_563_;
goto _start;
}
else
{
lean_object* v___x_567_; 
lean_inc(v_a_559_);
v___x_567_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_559_, v_id_551_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_577_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_a_568_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_562_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_567_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_567_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object* v_id_586_, lean_object* v_as_587_, lean_object* v_sz_588_, lean_object* v_i_589_, lean_object* v_b_590_, lean_object* v___y_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_588_);
lean_dec(v_sz_588_);
v_i_boxed_593_ = lean_unbox_usize(v_i_589_);
lean_dec(v_i_589_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_586_, v_as_587_, v_sz_boxed_592_, v_i_boxed_593_, v_b_590_);
lean_dec_ref(v_as_587_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object* v_db_597_, lean_object* v_id_598_){
_start:
{
lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_602_; size_t v_sz_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_600_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_597_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref(v___x_600_);
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_sz_603_ = lean_array_size(v_a_601_);
v___x_604_ = ((size_t)0ULL);
lean_inc_ref(v_id_598_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_598_, v_a_601_, v_sz_603_, v___x_604_, v___x_602_);
lean_dec(v_a_601_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_623_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_623_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_623_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_623_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_fst_610_; 
v_fst_610_ = lean_ctor_get(v_a_606_, 0);
lean_inc(v_fst_610_);
lean_dec(v_a_606_);
if (lean_obj_tag(v_fst_610_) == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_611_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__0));
v___x_612_ = lean_string_append(v___x_611_, v_id_598_);
lean_dec_ref(v_id_598_);
v___x_613_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__1));
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
v___x_615_ = lean_mk_io_user_error(v___x_614_);
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 1);
lean_ctor_set(v___x_608_, 0, v___x_615_);
v___x_617_ = v___x_608_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v_val_619_; lean_object* v___x_621_; 
lean_dec_ref(v_id_598_);
v_val_619_ = lean_ctor_get(v_fst_610_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v_fst_610_, 1);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_val_619_);
v___x_621_ = v___x_608_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_id_598_);
v_a_624_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_605_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_605_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object* v_db_632_, lean_object* v_id_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_632_, v_id_633_);
return v_res_635_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

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
lean_dec(v_a_14_);
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
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_303_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_304_ = lean_string_utf8_byte_size(v_tz_295_);
v___x_305_ = lean_obj_once(&l_Std_Time_Database_TZdb_parseTZValue___closed__1, &l_Std_Time_Database_TZdb_parseTZValue___closed__1_once, _init_l_Std_Time_Database_TZdb_parseTZValue___closed__1);
v___x_306_ = lean_nat_dec_le(v___x_305_, v___x_304_);
if (v___x_306_ == 0)
{
goto v___jp_296_;
}
else
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_string_memcmp(v_tz_295_, v___x_303_, v___x_307_, v___x_307_, v___x_305_);
if (v___x_308_ == 0)
{
goto v___jp_296_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_p_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_309_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_tz_295_);
v___x_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_310_, 0, v_tz_295_);
lean_ctor_set(v___x_310_, 1, v___x_307_);
lean_ctor_set(v___x_310_, 2, v___x_304_);
v___x_311_ = l_String_Slice_Pos_nextn(v___x_310_, v___x_307_, v___x_309_);
lean_dec_ref_known(v___x_310_, 3);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v_tz_295_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
lean_ctor_set(v___x_312_, 2, v___x_304_);
v_p_313_ = l_String_Slice_toString(v___x_312_);
lean_dec_ref_known(v___x_312_, 3);
v___x_314_ = lean_string_utf8_byte_size(v_p_313_);
v___x_315_ = lean_nat_dec_eq(v___x_314_, v___x_307_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v_p_313_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; 
lean_dec_ref(v_p_313_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = lean_string_utf8_byte_size(v_tz_295_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_tz_295_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v_tz_295_);
v___x_302_ = lean_box(0);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object* v_rel_322_, lean_object* v_as_323_, size_t v_sz_324_, size_t v_i_325_, lean_object* v_b_326_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec_ref(v_rel_322_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_b_326_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_331_; uint8_t v___x_332_; lean_object* v___x_333_; 
lean_dec_ref(v_b_326_);
v_a_330_ = lean_array_uget_borrowed(v_as_323_, v_i_325_);
lean_inc_ref(v_rel_322_);
lean_inc(v_a_330_);
v___x_331_ = l_System_FilePath_join(v_a_330_, v_rel_322_);
v___x_332_ = l_System_FilePath_pathExists(v___x_331_);
v___x_333_ = lean_box(0);
if (v___x_332_ == 0)
{
lean_object* v___x_334_; size_t v___x_335_; size_t v___x_336_; 
lean_dec_ref(v___x_331_);
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_325_, v___x_335_);
v_i_325_ = v___x_336_;
v_b_326_ = v___x_334_;
goto _start;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_rel_322_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_331_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_333_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object* v_rel_342_, lean_object* v_as_343_, lean_object* v_sz_344_, lean_object* v_i_345_, lean_object* v_b_346_, lean_object* v___y_347_){
_start:
{
size_t v_sz_boxed_348_; size_t v_i_boxed_349_; lean_object* v_res_350_; 
v_sz_boxed_348_ = lean_unbox_usize(v_sz_344_);
lean_dec(v_sz_344_);
v_i_boxed_349_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_342_, v_as_343_, v_sz_boxed_348_, v_i_boxed_349_, v_b_346_);
lean_dec_ref(v_as_343_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object* v_searchPaths_351_, lean_object* v_rel_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; size_t v_sz_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_354_ = lean_box(0);
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_sz_356_ = lean_array_size(v_searchPaths_351_);
v___x_357_ = ((size_t)0ULL);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_352_, v_searchPaths_351_, v_sz_356_, v___x_357_, v___x_355_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_371_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_371_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_371_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_371_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_fst_363_; 
v_fst_363_ = lean_ctor_get(v_a_359_, 0);
lean_inc(v_fst_363_);
lean_dec(v_a_359_);
if (lean_obj_tag(v_fst_363_) == 0)
{
lean_object* v___x_365_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_354_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_354_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_object* v_val_367_; lean_object* v___x_369_; 
v_val_367_ = lean_ctor_get(v_fst_363_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_fst_363_, 1);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v_val_367_);
v___x_369_ = v___x_361_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_val_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_358_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_358_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object* v_searchPaths_380_, lean_object* v_rel_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_380_, v_rel_381_);
lean_dec_ref(v_searchPaths_380_);
return v_res_383_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_resolveLocalPath___closed__4(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_389_ = lean_string_utf8_byte_size(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object* v_zonesPaths_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0));
v___x_395_ = lean_io_getenv(v___x_394_);
if (lean_obj_tag(v___x_395_) == 1)
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_477_; 
v_val_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_477_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_477_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_477_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; 
lean_inc(v_val_396_);
v___x_400_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_396_);
if (lean_obj_tag(v___x_400_) == 1)
{
lean_object* v_val_401_; 
lean_del_object(v___x_398_);
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v___x_400_, 1);
if (lean_obj_tag(v_val_401_) == 0)
{
lean_object* v_p_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_445_; 
v_p_402_ = lean_ctor_get(v_val_401_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_val_401_);
if (v_isSharedCheck_445_ == 0)
{
v___x_404_ = v_val_401_;
v_isShared_405_ = v_isSharedCheck_445_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_p_402_);
lean_dec(v_val_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_445_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_436_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_437_ = lean_string_utf8_byte_size(v_p_402_);
v___x_438_ = lean_obj_once(&l_Std_Time_Database_TZdb_resolveLocalPath___closed__4, &l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_once, _init_l_Std_Time_Database_TZdb_resolveLocalPath___closed__4);
v___x_439_ = lean_nat_dec_le(v___x_438_, v___x_437_);
if (v___x_439_ == 0)
{
lean_del_object(v___x_404_);
goto v___jp_406_;
}
else
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_string_memcmp(v_p_402_, v___x_436_, v___x_440_, v___x_440_, v___x_438_);
if (v___x_441_ == 0)
{
lean_del_object(v___x_404_);
goto v___jp_406_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v_val_396_);
if (v_isShared_405_ == 0)
{
v___x_443_ = v___x_404_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_p_402_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
v___jp_406_:
{
lean_object* v___x_407_; 
lean_inc_ref(v_p_402_);
v___x_407_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_392_, v_p_402_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_427_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_427_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_427_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_427_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v_val_412_; lean_object* v___x_414_; 
lean_dec_ref(v_p_402_);
lean_dec(v_val_396_);
v_val_412_ = lean_ctor_get(v_a_408_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v_a_408_, 1);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_val_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_val_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v_a_408_);
v___x_416_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_417_ = lean_string_append(v___x_416_, v_val_396_);
lean_dec(v_val_396_);
v___x_418_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2));
v___x_419_ = lean_string_append(v___x_417_, v___x_418_);
v___x_420_ = lean_string_append(v___x_419_, v_p_402_);
lean_dec_ref(v_p_402_);
v___x_421_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3));
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
v___x_423_ = lean_mk_io_user_error(v___x_422_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 1);
lean_ctor_set(v___x_410_, 0, v___x_423_);
v___x_425_ = v___x_410_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_p_402_);
lean_dec(v_val_396_);
v_a_428_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_407_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_407_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
else
{
lean_object* v_id_446_; lean_object* v___x_447_; 
v_id_446_ = lean_ctor_get(v_val_401_, 0);
lean_inc_ref(v_id_446_);
lean_dec_ref_known(v_val_401_, 1);
v___x_447_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_392_, v_id_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_464_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_464_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
if (lean_obj_tag(v_a_448_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_454_; 
lean_dec(v_val_396_);
v_val_452_ = lean_ctor_get(v_a_448_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v_a_448_, 1);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_val_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_val_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_a_448_);
v___x_456_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_457_ = lean_string_append(v___x_456_, v_val_396_);
lean_dec(v_val_396_);
v___x_458_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
v___x_460_ = lean_mk_io_user_error(v___x_459_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 0, v___x_460_);
v___x_462_ = v___x_450_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_val_396_);
v_a_465_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_447_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_447_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
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
}
else
{
lean_object* v___x_473_; lean_object* v___x_475_; 
lean_dec(v___x_400_);
lean_dec(v_val_396_);
v___x_473_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__6));
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 0);
lean_ctor_set(v___x_398_, 0, v___x_473_);
v___x_475_ = v___x_398_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_395_);
v___x_478_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__6));
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object* v_zonesPaths_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_480_);
lean_dec_ref(v_zonesPaths_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object* v_db_500_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0));
v___x_503_ = lean_io_getenv(v___x_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v_db_500_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_525_; 
v_val_505_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_525_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_525_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_525_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1));
v___x_510_ = lean_string_dec_eq(v_val_505_, v___x_509_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = l_System_FilePath_pathExists(v_val_505_);
if (v___x_511_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_val_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v_db_500_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_db_500_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_mk_empty_array_with_capacity(v___x_515_);
v___x_517_ = lean_array_push(v___x_516_, v_val_505_);
v___x_518_ = l_Array_append___redArg(v___x_517_, v_db_500_);
lean_dec_ref(v_db_500_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_518_);
v___x_520_ = v___x_507_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v___x_523_; 
lean_dec(v_val_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v_db_500_);
v___x_523_ = v___x_507_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_db_500_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object* v_db_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object* v_db_529_){
_start:
{
lean_object* v___x_531_; lean_object* v_a_532_; lean_object* v___x_533_; 
v___x_531_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_529_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v___x_533_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_532_);
lean_dec(v_a_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l_Std_Time_Database_TZdb_localRules(v_a_534_);
return v___x_535_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_a_536_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_533_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_533_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object* v_db_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object* v_id_550_, lean_object* v_as_551_, size_t v_sz_552_, size_t v_i_553_, lean_object* v_b_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_553_, v_sz_552_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec_ref(v_id_550_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_b_554_);
return v___x_557_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v_b_554_);
v_a_558_ = lean_array_uget_borrowed(v_as_551_, v_i_553_);
lean_inc_ref(v_id_550_);
lean_inc(v_a_558_);
v___x_559_ = l_System_FilePath_join(v_a_558_, v_id_550_);
v___x_560_ = l_System_FilePath_pathExists(v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = lean_box(0);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; size_t v___x_563_; size_t v___x_564_; 
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_553_, v___x_563_);
v_i_553_ = v___x_564_;
v_b_554_ = v___x_562_;
goto _start;
}
else
{
lean_object* v___x_566_; 
lean_inc(v_a_558_);
v___x_566_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_558_, v_id_550_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_576_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_576_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_a_567_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_561_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_566_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_566_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object* v_id_585_, lean_object* v_as_586_, lean_object* v_sz_587_, lean_object* v_i_588_, lean_object* v_b_589_, lean_object* v___y_590_){
_start:
{
size_t v_sz_boxed_591_; size_t v_i_boxed_592_; lean_object* v_res_593_; 
v_sz_boxed_591_ = lean_unbox_usize(v_sz_587_);
lean_dec(v_sz_587_);
v_i_boxed_592_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_585_, v_as_586_, v_sz_boxed_591_, v_i_boxed_592_, v_b_589_);
lean_dec_ref(v_as_586_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object* v_db_596_, lean_object* v_id_597_){
_start:
{
lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_601_; size_t v_sz_602_; size_t v___x_603_; lean_object* v___x_604_; 
v___x_599_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_596_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_sz_602_ = lean_array_size(v_a_600_);
v___x_603_ = ((size_t)0ULL);
lean_inc_ref(v_id_597_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_597_, v_a_600_, v_sz_602_, v___x_603_, v___x_601_);
lean_dec(v_a_600_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_622_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_622_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_622_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_622_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_fst_609_; 
v_fst_609_ = lean_ctor_get(v_a_605_, 0);
lean_inc(v_fst_609_);
lean_dec(v_a_605_);
if (lean_obj_tag(v_fst_609_) == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_610_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__0));
v___x_611_ = lean_string_append(v___x_610_, v_id_597_);
lean_dec_ref(v_id_597_);
v___x_612_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__1));
v___x_613_ = lean_string_append(v___x_611_, v___x_612_);
v___x_614_ = lean_mk_io_user_error(v___x_613_);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
lean_ctor_set(v___x_607_, 0, v___x_614_);
v___x_616_ = v___x_607_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v_val_618_; lean_object* v___x_620_; 
lean_dec_ref(v_id_597_);
v_val_618_ = lean_ctor_get(v_fst_609_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v_fst_609_, 1);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_val_618_);
v___x_620_ = v___x_607_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_val_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_id_597_);
v_a_623_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_604_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_604_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object* v_db_631_, lean_object* v_id_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_631_, v_id_632_);
return v_res_634_;
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

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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(lean_object* v_e_16_){
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
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_16_ = stack[0].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_16_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg___boxed(lean_object* v_e_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_36_);
return v_res_38_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(lean_object* v_00_u03b1_39_, lean_object* v_e_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_40_);
return v___x_42_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_40_ = stack[1].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(lean_box(0), v_e_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___boxed(lean_object* v_00_u03b1_44_, lean_object* v_e_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(v_00_u03b1_44_, v_e_45_);
return v_res_47_;
}
}
lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object* v_path_51_, lean_object* v_id_52_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_IO_FS_readBinFile(v_path_51_);
if (lean_obj_tag(v___x_54_) == 0)
{
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_54_, 1);
v___x_56_ = l_Std_Time_Database_TZdb_parseTZif(v_a_55_, v_id_52_);
v___x_57_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v___x_56_);
return v___x_57_;
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
lean_dec_ref(v_id_52_);
v_a_58_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_54_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 1);
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
else
{
lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_80_; 
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_54_, 0);
lean_dec(v_unused_81_);
v___x_67_ = v___x_54_;
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
else
{
lean_dec(v___x_54_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_69_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0));
v___x_70_ = lean_string_append(v___x_69_, v_id_52_);
lean_dec_ref(v_id_52_);
v___x_71_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1));
v___x_72_ = lean_string_append(v___x_70_, v___x_71_);
v___x_73_ = lean_string_append(v___x_72_, v_path_51_);
v___x_74_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2));
v___x_75_ = lean_string_append(v___x_73_, v___x_74_);
v___x_76_ = lean_mk_io_user_error(v___x_75_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_76_);
v___x_78_ = v___x_67_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_parseTZIfFromDisk_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_51_ = stack[0].m_obj;
lean_object* v_id_52_ = stack[1].m_obj;
lean_object* v_res_82_;
v_res_82_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_51_, v_id_52_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object* v_path_83_, lean_object* v_id_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_83_, v_id_84_);
lean_dec_ref(v_path_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object* v_path_89_){
_start:
{
lean_object* v___x_90_; lean_object* v_res_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_90_ = l_System_FilePath_components(v_path_89_);
v_res_91_ = lean_array_mk(v___x_90_);
v___x_92_ = lean_array_get_size(v_res_91_);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_sub(v___x_92_, v___x_93_);
v___x_95_ = lean_nat_dec_lt(v___x_94_, v___x_92_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec(v___x_94_);
lean_dec_ref(v_res_91_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lean_unsigned_to_nat(2u);
v___x_98_ = lean_nat_sub(v___x_92_, v___x_97_);
v___x_99_ = lean_nat_dec_lt(v___x_98_, v___x_92_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v___x_98_);
lean_dec(v___x_94_);
lean_dec_ref(v_res_91_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_101_ = lean_array_fget(v_res_91_, v___x_94_);
lean_dec(v___x_94_);
v___x_102_ = lean_array_fget(v_res_91_, v___x_98_);
lean_dec(v___x_98_);
lean_dec_ref(v_res_91_);
v___x_103_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__0));
v___x_104_ = lean_string_dec_eq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_str_109_; lean_object* v_startInclusive_110_; lean_object* v_endExclusive_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_129_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_string_utf8_byte_size(v___x_102_);
v___x_107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_102_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_106_);
v___x_108_ = l_String_Slice_trimAscii(v___x_107_);
v_str_109_ = lean_ctor_get(v___x_108_, 0);
v_startInclusive_110_ = lean_ctor_get(v___x_108_, 1);
v_endExclusive_111_ = lean_ctor_get(v___x_108_, 2);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_129_ == 0)
{
v___x_113_ = v___x_108_;
v_isShared_114_ = v_isSharedCheck_129_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_endExclusive_111_);
lean_inc(v_startInclusive_110_);
lean_inc(v_str_109_);
lean_dec(v___x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_129_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_string_utf8_byte_size(v___x_101_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 2, v___x_115_);
lean_ctor_set(v___x_113_, 1, v___x_105_);
lean_ctor_set(v___x_113_, 0, v___x_101_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v___x_115_);
v___x_117_ = v_reuseFailAlloc_128_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v_str_119_; lean_object* v_startInclusive_120_; lean_object* v_endExclusive_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_118_ = l_String_Slice_trimAscii(v___x_117_);
v_str_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_str_119_);
v_startInclusive_120_ = lean_ctor_get(v___x_118_, 1);
lean_inc(v_startInclusive_120_);
v_endExclusive_121_ = lean_ctor_get(v___x_118_, 2);
lean_inc(v_endExclusive_121_);
lean_dec_ref(v___x_118_);
v___x_122_ = lean_string_utf8_extract_fast(v_str_109_, v_startInclusive_110_, v_endExclusive_111_);
lean_dec(v_endExclusive_111_);
lean_dec(v_startInclusive_110_);
lean_dec_ref(v_str_109_);
v___x_123_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = lean_string_utf8_extract_fast(v_str_119_, v_startInclusive_120_, v_endExclusive_121_);
lean_dec(v_endExclusive_121_);
lean_dec(v_startInclusive_120_);
lean_dec_ref(v_str_119_);
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_str_134_; lean_object* v_startInclusive_135_; lean_object* v_endExclusive_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v___x_102_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_string_utf8_byte_size(v___x_101_);
v___x_132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_101_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
v___x_133_ = l_String_Slice_trimAscii(v___x_132_);
v_str_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_str_134_);
v_startInclusive_135_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_startInclusive_135_);
v_endExclusive_136_ = lean_ctor_get(v___x_133_, 2);
lean_inc(v_endExclusive_136_);
lean_dec_ref(v___x_133_);
v___x_137_ = lean_string_utf8_extract_fast(v_str_134_, v_startInclusive_135_, v_endExclusive_136_);
lean_dec(v_endExclusive_136_);
lean_dec(v_startInclusive_135_);
lean_dec_ref(v_str_134_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Std_Time_Database_TZdb_localRules___closed__0));
v___x_141_ = lean_mk_io_user_error(v___x_140_);
return v___x_141_;
}
}
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object* v_path_142_){
_start:
{
lean_object* v___x_144_; 
lean_inc_ref(v_path_142_);
v___x_144_ = lean_io_realpath(v_path_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_156_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_156_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Time_Database_TZdb_idFromPath(v_a_145_);
if (lean_obj_tag(v___x_149_) == 1)
{
lean_object* v_val_150_; lean_object* v___x_151_; 
lean_del_object(v___x_147_);
v_val_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v___x_149_, 1);
v___x_151_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_142_, v_val_150_);
lean_dec_ref(v_path_142_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_154_; 
lean_dec(v___x_149_);
lean_dec_ref(v_path_142_);
v___x_152_ = lean_obj_once(&l_Std_Time_Database_TZdb_localRules___closed__1, &l_Std_Time_Database_TZdb_localRules___closed__1_once, _init_l_Std_Time_Database_TZdb_localRules___closed__1);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 1);
lean_ctor_set(v___x_147_, 0, v___x_152_);
v___x_154_ = v___x_147_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v_path_142_);
v_a_157_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_144_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_144_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_localRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_142_ = stack[0].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Std_Time_Database_TZdb_localRules(v_path_142_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___boxed(lean_object* v_path_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Time_Database_TZdb_localRules(v_path_166_);
return v_res_168_;
}
}
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object* v_path_169_, lean_object* v_id_170_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_inc_ref(v_id_170_);
v___x_172_ = l_System_FilePath_join(v_path_169_, v_id_170_);
v___x_173_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v___x_172_, v_id_170_);
lean_dec_ref(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_readRulesFromDisk_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_169_ = stack[0].m_obj;
lean_object* v_id_170_ = stack[1].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_path_169_, v_id_170_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(lean_object* v_path_175_, lean_object* v_id_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_path_175_, v_id_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_tag_nat(v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl___boxed(lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(v_x_181_);
lean_dec_ref(v_x_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(lean_object* v_t_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_p_185_; lean_object* v___x_186_; 
v_p_185_ = lean_ctor_get(v_t_183_, 0);
lean_inc_ref(v_p_185_);
lean_dec_ref(v_t_183_);
v___x_186_ = lean_apply_1(v_k_184_, v_p_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_189_, v_k_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___boxed(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim(v_motive_193_, v_ctorIdx_194_, v_t_195_, v_h_196_, v_k_197_);
lean_dec(v_ctorIdx_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim___redArg(lean_object* v_t_199_, lean_object* v_filePath_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_199_, v_filePath_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_filePath_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_203_, v_filePath_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim___redArg(lean_object* v_t_207_, lean_object* v_zoneId_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_207_, v_zoneId_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_zoneId_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_211_, v_zoneId_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(2u);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_to_int(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr(lean_object* v_x_231_, lean_object* v_prec_232_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v_p_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_253_; 
v_p_233_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_253_ == 0)
{
v___x_235_ = v_x_231_;
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_p_233_);
lean_dec(v_x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___y_238_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = lean_nat_dec_le(v___x_249_, v_prec_232_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_238_ = v___x_251_;
goto v___jp_237_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_238_ = v___x_252_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2));
v___x_240_ = l_String_quote(v_p_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 3);
lean_ctor_set(v___x_235_, 0, v___x_240_);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_248_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_239_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_inc(v___y_238_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___y_238_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = l_Repr_addAppParen(v___x_246_, v_prec_232_);
return v___x_247_;
}
}
}
}
else
{
lean_object* v_id_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_274_; 
v_id_254_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_274_ == 0)
{
v___x_256_ = v_x_231_;
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_id_254_);
lean_dec(v_x_231_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___y_259_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1024u);
v___x_271_ = lean_nat_dec_le(v___x_270_, v_prec_232_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_259_ = v___x_272_;
goto v___jp_258_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_259_ = v___x_273_;
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_260_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7));
v___x_261_ = l_String_quote(v_id_254_);
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 3);
lean_ctor_set(v___x_256_, 0, v___x_261_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_269_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_260_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_inc(v___y_259_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_259_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___x_268_ = l_Repr_addAppParen(v___x_267_, v_prec_232_);
return v___x_268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed(lean_object* v_x_275_, lean_object* v_prec_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr(v_x_275_, v_prec_276_);
lean_dec(v_prec_276_);
return v_res_277_;
}
}
uint8_t l_Std_Time_Database_TZdb_instBEqTZSpec_beq(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_p_282_; lean_object* v_p_283_; uint8_t v___x_284_; 
v_p_282_ = lean_ctor_get(v_x_280_, 0);
v_p_283_ = lean_ctor_get(v_x_281_, 0);
v___x_284_ = lean_string_dec_eq(v_p_282_, v_p_283_);
return v___x_284_;
}
else
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
else
{
if (lean_obj_tag(v_x_281_) == 1)
{
lean_object* v_id_286_; lean_object* v_id_287_; uint8_t v___x_288_; 
v_id_286_ = lean_ctor_get(v_x_280_, 0);
v_id_287_ = lean_ctor_get(v_x_281_, 0);
v___x_288_ = lean_string_dec_eq(v_id_286_, v_id_287_);
return v___x_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_instBEqTZSpec_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_280_ = stack[0].m_obj;
lean_object* v_x_281_ = stack[1].m_obj;
uint8_t v_res_290_;
v_res_290_ = l_Std_Time_Database_TZdb_instBEqTZSpec_beq(v_x_280_, v_x_281_);
stack->m_num = v_res_290_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed(lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_Time_Database_TZdb_instBEqTZSpec_beq(v_x_291_, v_x_292_);
lean_dec_ref(v_x_292_);
lean_dec_ref(v_x_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZValue(lean_object* v_tz_298_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = lean_string_utf8_byte_size(v_tz_298_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_dec_le(v___x_307_, v___x_306_);
if (v___x_308_ == 0)
{
goto v___jp_299_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_string_memcmp(v_tz_298_, v___x_309_, v___x_310_, v___x_310_, v___x_307_);
if (v___x_311_ == 0)
{
goto v___jp_299_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_p_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
lean_inc_ref(v_tz_298_);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v_tz_298_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_306_);
v___x_313_ = l_String_Slice_Pos_nextn(v___x_312_, v___x_310_, v___x_307_);
lean_dec_ref_known(v___x_312_, 3);
v___x_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_314_, 0, v_tz_298_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
lean_ctor_set(v___x_314_, 2, v___x_306_);
v_p_315_ = l_String_Slice_toString(v___x_314_);
lean_dec_ref_known(v___x_314_, 3);
v___x_316_ = lean_string_utf8_byte_size(v_p_315_);
v___x_317_ = lean_nat_dec_eq(v___x_316_, v___x_310_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v_p_315_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; 
lean_dec_ref(v_p_315_);
v___x_320_ = lean_box(0);
return v___x_320_;
}
}
}
v___jp_299_:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_string_utf8_byte_size(v_tz_298_);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_nat_dec_eq(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_tz_298_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_dec_ref(v_tz_298_);
v___x_305_ = lean_box(0);
return v___x_305_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object* v_rel_324_, lean_object* v_as_325_, size_t v_sz_326_, size_t v_i_327_, lean_object* v_b_328_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_rel_324_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_b_328_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
lean_dec_ref(v_b_328_);
v___x_332_ = lean_box(0);
v___x_333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_a_334_ = lean_array_uget_borrowed(v_as_325_, v_i_327_);
lean_inc_ref(v_rel_324_);
lean_inc(v_a_334_);
v___x_335_ = l_System_FilePath_join(v_a_334_, v_rel_324_);
v___x_336_ = l_System_FilePath_pathExists(v___x_335_);
if (v___x_336_ == 0)
{
size_t v___x_337_; size_t v___x_338_; 
lean_dec_ref(v___x_335_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_327_, v___x_337_);
v_i_327_ = v___x_338_;
v_b_328_ = v___x_333_;
goto _start;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec_ref(v_rel_324_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_335_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_332_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_rel_324_ = stack[0].m_obj;
lean_object* v_as_325_ = stack[1].m_obj;
size_t v_sz_326_ = stack[2].m_num;
size_t v_i_327_ = stack[3].m_num;
lean_object* v_b_328_ = stack[4].m_obj;
lean_object* v_res_344_;
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_324_, v_as_325_, v_sz_326_, v_i_327_, v_b_328_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object* v_rel_345_, lean_object* v_as_346_, lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_b_349_, lean_object* v___y_350_){
_start:
{
size_t v_sz_boxed_351_; size_t v_i_boxed_352_; lean_object* v_res_353_; 
v_sz_boxed_351_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_352_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_345_, v_as_346_, v_sz_boxed_351_, v_i_boxed_352_, v_b_349_);
lean_dec_ref(v_as_346_);
return v_res_353_;
}
}
lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object* v_searchPaths_354_, lean_object* v_rel_355_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; size_t v_sz_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___x_357_ = lean_box(0);
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_sz_359_ = lean_array_size(v_searchPaths_354_);
v___x_360_ = ((size_t)0ULL);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_355_, v_searchPaths_354_, v_sz_359_, v___x_360_, v___x_358_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_374_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_374_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_fst_366_; 
v_fst_366_ = lean_ctor_get(v_a_362_, 0);
lean_inc(v_fst_366_);
lean_dec(v_a_362_);
if (lean_obj_tag(v_fst_366_) == 0)
{
lean_object* v___x_368_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_357_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_357_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v_val_370_; lean_object* v___x_372_; 
v_val_370_ = lean_ctor_get(v_fst_366_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_fst_366_, 1);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_val_370_);
v___x_372_ = v___x_364_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_val_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_361_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_361_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_findInPaths_0interp(lean_interpreter_value* stack)
{
lean_object* v_searchPaths_354_ = stack[0].m_obj;
lean_object* v_rel_355_ = stack[1].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_354_, v_rel_355_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object* v_searchPaths_384_, lean_object* v_rel_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_384_, v_rel_385_);
lean_dec_ref(v_searchPaths_384_);
return v_res_387_;
}
}
lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object* v_zonesPaths_394_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0));
v___x_397_ = lean_io_getenv(v___x_396_);
if (lean_obj_tag(v___x_397_) == 1)
{
lean_object* v_val_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_479_; 
v_val_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_479_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_479_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_val_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_479_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; 
lean_inc(v_val_398_);
v___x_402_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_398_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; 
lean_del_object(v___x_400_);
v_val_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_402_, 1);
if (lean_obj_tag(v_val_403_) == 0)
{
lean_object* v_p_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_447_; 
v_p_404_ = lean_ctor_get(v_val_403_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_val_403_);
if (v_isSharedCheck_447_ == 0)
{
v___x_406_ = v_val_403_;
v_isShared_407_ = v_isSharedCheck_447_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_p_404_);
lean_dec(v_val_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_447_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_string_utf8_byte_size(v_p_404_);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_dec_le(v___x_439_, v___x_438_);
if (v___x_440_ == 0)
{
lean_del_object(v___x_406_);
goto v___jp_408_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_string_memcmp(v_p_404_, v___x_441_, v___x_442_, v___x_442_, v___x_439_);
if (v___x_443_ == 0)
{
lean_del_object(v___x_406_);
goto v___jp_408_;
}
else
{
lean_object* v___x_445_; 
lean_dec(v_val_398_);
if (v_isShared_407_ == 0)
{
v___x_445_ = v___x_406_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_p_404_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
v___jp_408_:
{
lean_object* v___x_409_; 
lean_inc_ref(v_p_404_);
v___x_409_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_394_, v_p_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_429_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_429_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_429_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_429_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
if (lean_obj_tag(v_a_410_) == 1)
{
lean_object* v_val_414_; lean_object* v___x_416_; 
lean_dec_ref(v_p_404_);
lean_dec(v_val_398_);
v_val_414_ = lean_ctor_get(v_a_410_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v_a_410_, 1);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v_val_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_val_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_a_410_);
v___x_418_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_419_ = lean_string_append(v___x_418_, v_val_398_);
lean_dec(v_val_398_);
v___x_420_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2));
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = lean_string_append(v___x_421_, v_p_404_);
lean_dec_ref(v_p_404_);
v___x_423_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3));
v___x_424_ = lean_string_append(v___x_422_, v___x_423_);
v___x_425_ = lean_mk_io_user_error(v___x_424_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 1);
lean_ctor_set(v___x_412_, 0, v___x_425_);
v___x_427_ = v___x_412_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_p_404_);
lean_dec(v_val_398_);
v_a_430_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_409_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_409_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
else
{
lean_object* v_id_448_; lean_object* v___x_449_; 
v_id_448_ = lean_ctor_get(v_val_403_, 0);
lean_inc_ref(v_id_448_);
lean_dec_ref_known(v_val_403_, 1);
v___x_449_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_394_, v_id_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_466_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_466_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_466_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_466_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
if (lean_obj_tag(v_a_450_) == 1)
{
lean_object* v_val_454_; lean_object* v___x_456_; 
lean_dec(v_val_398_);
v_val_454_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_val_454_);
lean_dec_ref_known(v_a_450_, 1);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_val_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_val_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
lean_dec(v_a_450_);
v___x_458_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_459_ = lean_string_append(v___x_458_, v_val_398_);
lean_dec(v_val_398_);
v___x_460_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__4));
v___x_461_ = lean_string_append(v___x_459_, v___x_460_);
v___x_462_ = lean_mk_io_user_error(v___x_461_);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 1);
lean_ctor_set(v___x_452_, 0, v___x_462_);
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_val_398_);
v_a_467_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_449_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_449_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v___x_402_);
lean_dec(v_val_398_);
v___x_475_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 0);
lean_ctor_set(v___x_400_, 0, v___x_475_);
v___x_477_ = v___x_400_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v___x_397_);
v___x_480_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_resolveLocalPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_zonesPaths_394_ = stack[0].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_394_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object* v_zonesPaths_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_483_);
lean_dec_ref(v_zonesPaths_483_);
return v_res_485_;
}
}
lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object* v_db_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0));
v___x_506_ = lean_io_getenv(v___x_505_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v_db_503_);
return v___x_507_;
}
else
{
lean_object* v_val_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_528_; 
v_val_508_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_528_ == 0)
{
v___x_510_ = v___x_506_;
v_isShared_511_ = v_isSharedCheck_528_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_val_508_);
lean_dec(v___x_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_528_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1));
v___x_513_ = lean_string_dec_eq(v_val_508_, v___x_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; 
v___x_514_ = l_System_FilePath_pathExists(v_val_508_);
if (v___x_514_ == 0)
{
lean_object* v___x_516_; 
lean_dec(v_val_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 0);
lean_ctor_set(v___x_510_, 0, v_db_503_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_db_503_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_520_ = lean_array_push(v___x_519_, v_val_508_);
v___x_521_ = l_Array_append___redArg(v___x_520_, v_db_503_);
lean_dec_ref(v_db_503_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 0);
lean_ctor_set(v___x_510_, 0, v___x_521_);
v___x_523_ = v___x_510_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v___x_526_; 
lean_dec(v_val_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 0);
lean_ctor_set(v___x_510_, 0, v_db_503_);
v___x_526_ = v___x_510_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_db_503_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_resolveZonesPaths_0interp(lean_interpreter_value* stack)
{
lean_object* v_db_503_ = stack[0].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_503_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object* v_db_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_530_);
return v_res_532_;
}
}
lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object* v_db_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_a_536_; lean_object* v___x_537_; 
v___x_535_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_533_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v___x_537_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_536_);
lean_dec(v_a_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Std_Time_Database_TZdb_localRules(v_a_538_);
return v___x_539_;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_537_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_537_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_getLocalZoneRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_db_533_ = stack[0].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_533_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object* v_db_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_549_);
return v_res_551_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object* v_id_555_, lean_object* v_as_556_, size_t v_sz_557_, size_t v_i_558_, lean_object* v_b_559_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_lt(v_i_558_, v_sz_557_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_dec_ref(v_id_555_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_b_559_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec_ref(v_b_559_);
v___x_563_ = lean_box(0);
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_a_565_ = lean_array_uget_borrowed(v_as_556_, v_i_558_);
lean_inc_ref(v_id_555_);
lean_inc(v_a_565_);
v___x_566_ = l_System_FilePath_join(v_a_565_, v_id_555_);
v___x_567_ = l_System_FilePath_pathExists(v___x_566_);
lean_dec_ref(v___x_566_);
if (v___x_567_ == 0)
{
size_t v___x_568_; size_t v___x_569_; 
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_558_, v___x_568_);
v_i_558_ = v___x_569_;
v_b_559_ = v___x_564_;
goto _start;
}
else
{
lean_object* v___x_571_; 
lean_inc(v_a_565_);
v___x_571_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_565_, v_id_555_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_581_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_581_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_581_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_581_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v_a_572_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_563_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_571_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_571_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_555_ = stack[0].m_obj;
lean_object* v_as_556_ = stack[1].m_obj;
size_t v_sz_557_ = stack[2].m_num;
size_t v_i_558_ = stack[3].m_num;
lean_object* v_b_559_ = stack[4].m_obj;
lean_object* v_res_590_;
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_555_, v_as_556_, v_sz_557_, v_i_558_, v_b_559_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object* v_id_591_, lean_object* v_as_592_, lean_object* v_sz_593_, lean_object* v_i_594_, lean_object* v_b_595_, lean_object* v___y_596_){
_start:
{
size_t v_sz_boxed_597_; size_t v_i_boxed_598_; lean_object* v_res_599_; 
v_sz_boxed_597_ = lean_unbox_usize(v_sz_593_);
lean_dec(v_sz_593_);
v_i_boxed_598_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_591_, v_as_592_, v_sz_boxed_597_, v_i_boxed_598_, v_b_595_);
lean_dec_ref(v_as_592_);
return v_res_599_;
}
}
lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object* v_db_602_, lean_object* v_id_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_a_606_; lean_object* v___x_607_; size_t v_sz_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_605_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_602_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref(v___x_605_);
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_sz_608_ = lean_array_size(v_a_606_);
v___x_609_ = ((size_t)0ULL);
lean_inc_ref(v_id_603_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_603_, v_a_606_, v_sz_608_, v___x_609_, v___x_607_);
lean_dec(v_a_606_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_628_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_628_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_628_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_628_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; 
v_fst_615_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_fst_615_);
lean_dec(v_a_611_);
if (lean_obj_tag(v_fst_615_) == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_616_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__0));
v___x_617_ = lean_string_append(v___x_616_, v_id_603_);
lean_dec_ref(v_id_603_);
v___x_618_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__1));
v___x_619_ = lean_string_append(v___x_617_, v___x_618_);
v___x_620_ = lean_mk_io_user_error(v___x_619_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 1);
lean_ctor_set(v___x_613_, 0, v___x_620_);
v___x_622_ = v___x_613_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v_val_624_; lean_object* v___x_626_; 
lean_dec_ref(v_id_603_);
v_val_624_ = lean_ctor_get(v_fst_615_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_fst_615_, 1);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_val_624_);
v___x_626_ = v___x_613_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_val_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_id_603_);
v_a_629_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_610_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_610_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_TZdb_getZoneRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_db_602_ = stack[0].m_obj;
lean_object* v_id_603_ = stack[1].m_obj;
lean_object* v_res_637_;
v_res_637_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_602_, v_id_603_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object* v_db_638_, lean_object* v_id_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_638_, v_id_639_);
return v_res_641_;
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

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
lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_70_; 
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_70_ == 0)
{
lean_object* v_unused_71_; 
v_unused_71_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_71_);
v___x_57_ = v___x_52_;
v_isShared_58_ = v_isSharedCheck_70_;
goto v_resetjp_56_;
}
else
{
lean_dec(v___x_52_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_70_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_59_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0));
v___x_60_ = lean_string_append(v___x_59_, v_id_50_);
lean_dec_ref(v_id_50_);
v___x_61_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1));
v___x_62_ = lean_string_append(v___x_60_, v___x_61_);
v___x_63_ = lean_string_append(v___x_62_, v_path_49_);
v___x_64_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2));
v___x_65_ = lean_string_append(v___x_63_, v___x_64_);
v___x_66_ = lean_mk_io_user_error(v___x_65_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_66_);
v___x_68_ = v___x_57_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object* v_path_72_, lean_object* v_id_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_72_, v_id_73_);
lean_dec_ref(v_path_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object* v_path_78_){
_start:
{
lean_object* v___x_79_; lean_object* v_res_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_79_ = l_System_FilePath_components(v_path_78_);
v_res_80_ = lean_array_mk(v___x_79_);
v___x_81_ = lean_array_get_size(v_res_80_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_sub(v___x_81_, v___x_82_);
v___x_84_ = lean_nat_dec_lt(v___x_83_, v___x_81_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec(v___x_83_);
lean_dec_ref(v_res_80_);
v___x_85_ = lean_box(0);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_unsigned_to_nat(2u);
v___x_87_ = lean_nat_sub(v___x_81_, v___x_86_);
v___x_88_ = lean_nat_dec_lt(v___x_87_, v___x_81_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec(v___x_87_);
lean_dec(v___x_83_);
lean_dec_ref(v_res_80_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_90_ = lean_array_fget(v_res_80_, v___x_83_);
lean_dec(v___x_83_);
v___x_91_ = lean_array_fget(v_res_80_, v___x_87_);
lean_dec(v___x_87_);
lean_dec_ref(v_res_80_);
v___x_92_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__0));
v___x_93_ = lean_string_dec_eq(v___x_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_str_98_; lean_object* v_startInclusive_99_; lean_object* v_endExclusive_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_118_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_string_utf8_byte_size(v___x_91_);
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
v___x_97_ = l_String_Slice_trimAscii(v___x_96_);
v_str_98_ = lean_ctor_get(v___x_97_, 0);
v_startInclusive_99_ = lean_ctor_get(v___x_97_, 1);
v_endExclusive_100_ = lean_ctor_get(v___x_97_, 2);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_118_ == 0)
{
v___x_102_ = v___x_97_;
v_isShared_103_ = v_isSharedCheck_118_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_endExclusive_100_);
lean_inc(v_startInclusive_99_);
lean_inc(v_str_98_);
lean_dec(v___x_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_118_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_string_utf8_byte_size(v___x_90_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_104_);
lean_ctor_set(v___x_102_, 1, v___x_94_);
lean_ctor_set(v___x_102_, 0, v___x_90_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v___x_104_);
v___x_106_ = v_reuseFailAlloc_117_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v_str_108_; lean_object* v_startInclusive_109_; lean_object* v_endExclusive_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_107_ = l_String_Slice_trimAscii(v___x_106_);
v_str_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_str_108_);
v_startInclusive_109_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_startInclusive_109_);
v_endExclusive_110_ = lean_ctor_get(v___x_107_, 2);
lean_inc(v_endExclusive_110_);
lean_dec_ref(v___x_107_);
v___x_111_ = lean_string_utf8_extract_fast(v_str_98_, v_startInclusive_99_, v_endExclusive_100_);
lean_dec(v_endExclusive_100_);
lean_dec(v_startInclusive_99_);
lean_dec_ref(v_str_98_);
v___x_112_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_113_ = lean_string_append(v___x_111_, v___x_112_);
v___x_114_ = lean_string_utf8_extract_fast(v_str_108_, v_startInclusive_109_, v_endExclusive_110_);
lean_dec(v_endExclusive_110_);
lean_dec(v_startInclusive_109_);
lean_dec_ref(v_str_108_);
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
lean_dec_ref(v___x_114_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_str_123_; lean_object* v_startInclusive_124_; lean_object* v_endExclusive_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v___x_91_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_string_utf8_byte_size(v___x_90_);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_90_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
v___x_122_ = l_String_Slice_trimAscii(v___x_121_);
v_str_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref(v_str_123_);
v_startInclusive_124_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_startInclusive_124_);
v_endExclusive_125_ = lean_ctor_get(v___x_122_, 2);
lean_inc(v_endExclusive_125_);
lean_dec_ref(v___x_122_);
v___x_126_ = lean_string_utf8_extract_fast(v_str_123_, v_startInclusive_124_, v_endExclusive_125_);
lean_dec(v_endExclusive_125_);
lean_dec(v_startInclusive_124_);
lean_dec_ref(v_str_123_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__1(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l_Std_Time_Database_TZdb_localRules___closed__0));
v___x_130_ = lean_mk_io_user_error(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object* v_path_131_){
_start:
{
lean_object* v___x_133_; 
lean_inc_ref(v_path_131_);
v___x_133_ = lean_io_realpath(v_path_131_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_145_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_145_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; 
v___x_138_ = l_Std_Time_Database_TZdb_idFromPath(v_a_134_);
if (lean_obj_tag(v___x_138_) == 1)
{
lean_object* v_val_139_; lean_object* v___x_140_; 
lean_del_object(v___x_136_);
v_val_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_131_, v_val_139_);
lean_dec_ref(v_path_131_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_143_; 
lean_dec(v___x_138_);
lean_dec_ref(v_path_131_);
v___x_141_ = lean_obj_once(&l_Std_Time_Database_TZdb_localRules___closed__1, &l_Std_Time_Database_TZdb_localRules___closed__1_once, _init_l_Std_Time_Database_TZdb_localRules___closed__1);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 1);
lean_ctor_set(v___x_136_, 0, v___x_141_);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v_path_131_);
v_a_146_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_133_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_133_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
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
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___boxed(lean_object* v_path_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_Database_TZdb_localRules(v_path_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object* v_path_157_, lean_object* v_id_158_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc_ref(v_id_158_);
v___x_160_ = l_System_FilePath_join(v_path_157_, v_id_158_);
v___x_161_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v___x_160_, v_id_158_);
lean_dec_ref(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(lean_object* v_path_162_, lean_object* v_id_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_path_162_, v_id_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(lean_object* v_x_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_tag_nat(v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl___boxed(lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(v_x_168_);
lean_dec_ref(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(lean_object* v_t_170_, lean_object* v_k_171_){
_start:
{
lean_object* v_p_172_; lean_object* v___x_173_; 
v_p_172_ = lean_ctor_get(v_t_170_, 0);
lean_inc_ref(v_p_172_);
lean_dec_ref(v_t_170_);
v___x_173_ = lean_apply_1(v_k_171_, v_p_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim(lean_object* v_motive_174_, lean_object* v_ctorIdx_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_k_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_176_, v_k_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___boxed(lean_object* v_motive_180_, lean_object* v_ctorIdx_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim(v_motive_180_, v_ctorIdx_181_, v_t_182_, v_h_183_, v_k_184_);
lean_dec(v_ctorIdx_181_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim___redArg(lean_object* v_t_186_, lean_object* v_filePath_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_186_, v_filePath_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim(lean_object* v_motive_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_filePath_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_190_, v_filePath_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim___redArg(lean_object* v_t_194_, lean_object* v_zoneId_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_194_, v_zoneId_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_zoneId_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_198_, v_zoneId_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = lean_nat_to_int(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_to_int(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr(lean_object* v_x_218_, lean_object* v_prec_219_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v_p_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_240_; 
v_p_220_ = lean_ctor_get(v_x_218_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_240_ == 0)
{
v___x_222_ = v_x_218_;
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_p_220_);
lean_dec(v_x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___y_225_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1024u);
v___x_237_ = lean_nat_dec_le(v___x_236_, v_prec_219_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_225_ = v___x_238_;
goto v___jp_224_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2));
v___x_227_ = l_String_quote(v_p_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 3);
lean_ctor_set(v___x_222_, 0, v___x_227_);
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_235_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_226_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
lean_inc(v___y_225_);
v___x_231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_231_, 0, v___y_225_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = 0;
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_232_);
v___x_234_ = l_Repr_addAppParen(v___x_233_, v_prec_219_);
return v___x_234_;
}
}
}
}
else
{
lean_object* v_id_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_261_; 
v_id_241_ = lean_ctor_get(v_x_218_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_261_ == 0)
{
v___x_243_ = v_x_218_;
v_isShared_244_ = v_isSharedCheck_261_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_id_241_);
lean_dec(v_x_218_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_261_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___y_246_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1024u);
v___x_258_ = lean_nat_dec_le(v___x_257_, v_prec_219_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_246_ = v___x_259_;
goto v___jp_245_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_246_ = v___x_260_;
goto v___jp_245_;
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7));
v___x_248_ = l_String_quote(v_id_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 3);
lean_ctor_set(v___x_243_, 0, v___x_248_);
v___x_250_ = v___x_243_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_256_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_247_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc(v___y_246_);
v___x_252_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_252_, 0, v___y_246_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = 0;
v___x_254_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*1, v___x_253_);
v___x_255_ = l_Repr_addAppParen(v___x_254_, v_prec_219_);
return v___x_255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed(lean_object* v_x_262_, lean_object* v_prec_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr(v_x_262_, v_prec_263_);
lean_dec(v_prec_263_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Database_TZdb_instBEqTZSpec_beq(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v_p_269_; lean_object* v_p_270_; uint8_t v___x_271_; 
v_p_269_ = lean_ctor_get(v_x_267_, 0);
v_p_270_ = lean_ctor_get(v_x_268_, 0);
v___x_271_ = lean_string_dec_eq(v_p_269_, v_p_270_);
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
else
{
if (lean_obj_tag(v_x_268_) == 1)
{
lean_object* v_id_273_; lean_object* v_id_274_; uint8_t v___x_275_; 
v_id_273_ = lean_ctor_get(v_x_267_, 0);
v_id_274_ = lean_ctor_get(v_x_268_, 0);
v___x_275_ = lean_string_dec_eq(v_id_273_, v_id_274_);
return v___x_275_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = 0;
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_Time_Database_TZdb_instBEqTZSpec_beq(v_x_277_, v_x_278_);
lean_dec_ref(v_x_278_);
lean_dec_ref(v_x_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZValue(lean_object* v_tz_284_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_string_utf8_byte_size(v_tz_284_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_dec_le(v___x_293_, v___x_292_);
if (v___x_294_ == 0)
{
goto v___jp_285_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_string_memcmp(v_tz_284_, v___x_295_, v___x_296_, v___x_296_, v___x_293_);
if (v___x_297_ == 0)
{
goto v___jp_285_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_p_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
lean_inc_ref(v_tz_284_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v_tz_284_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
lean_ctor_set(v___x_298_, 2, v___x_292_);
v___x_299_ = l_String_Slice_Pos_nextn(v___x_298_, v___x_296_, v___x_293_);
lean_dec_ref_known(v___x_298_, 3);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v_tz_284_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
lean_ctor_set(v___x_300_, 2, v___x_292_);
v_p_301_ = l_String_Slice_toString(v___x_300_);
lean_dec_ref_known(v___x_300_, 3);
v___x_302_ = lean_string_utf8_byte_size(v_p_301_);
v___x_303_ = lean_nat_dec_eq(v___x_302_, v___x_296_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_p_301_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec_ref(v_p_301_);
v___x_306_ = lean_box(0);
return v___x_306_;
}
}
}
v___jp_285_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_string_utf8_byte_size(v_tz_284_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_tz_284_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; 
lean_dec_ref(v_tz_284_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object* v_rel_310_, lean_object* v_as_311_, size_t v_sz_312_, size_t v_i_313_, lean_object* v_b_314_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_lt(v_i_313_, v_sz_312_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v_rel_310_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_b_314_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
lean_dec_ref(v_b_314_);
v___x_318_ = lean_box(0);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_a_320_ = lean_array_uget_borrowed(v_as_311_, v_i_313_);
lean_inc_ref(v_rel_310_);
lean_inc(v_a_320_);
v___x_321_ = l_System_FilePath_join(v_a_320_, v_rel_310_);
v___x_322_ = l_System_FilePath_pathExists(v___x_321_);
if (v___x_322_ == 0)
{
size_t v___x_323_; size_t v___x_324_; 
lean_dec_ref(v___x_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_313_, v___x_323_);
v_i_313_ = v___x_324_;
v_b_314_ = v___x_319_;
goto _start;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_rel_310_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_321_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_318_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object* v_rel_330_, lean_object* v_as_331_, lean_object* v_sz_332_, lean_object* v_i_333_, lean_object* v_b_334_, lean_object* v___y_335_){
_start:
{
size_t v_sz_boxed_336_; size_t v_i_boxed_337_; lean_object* v_res_338_; 
v_sz_boxed_336_ = lean_unbox_usize(v_sz_332_);
lean_dec(v_sz_332_);
v_i_boxed_337_ = lean_unbox_usize(v_i_333_);
lean_dec(v_i_333_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_330_, v_as_331_, v_sz_boxed_336_, v_i_boxed_337_, v_b_334_);
lean_dec_ref(v_as_331_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object* v_searchPaths_339_, lean_object* v_rel_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; size_t v_sz_344_; size_t v___x_345_; lean_object* v___x_346_; 
v___x_342_ = lean_box(0);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_sz_344_ = lean_array_size(v_searchPaths_339_);
v___x_345_ = ((size_t)0ULL);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_340_, v_searchPaths_339_, v_sz_344_, v___x_345_, v___x_343_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_359_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_359_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_fst_351_; 
v_fst_351_ = lean_ctor_get(v_a_347_, 0);
lean_inc(v_fst_351_);
lean_dec(v_a_347_);
if (lean_obj_tag(v_fst_351_) == 0)
{
lean_object* v___x_353_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_342_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_342_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_val_355_; lean_object* v___x_357_; 
v_val_355_ = lean_ctor_get(v_fst_351_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v_fst_351_, 1);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_val_355_);
v___x_357_ = v___x_349_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_val_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_346_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_346_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object* v_searchPaths_368_, lean_object* v_rel_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_368_, v_rel_369_);
lean_dec_ref(v_searchPaths_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object* v_zonesPaths_378_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0));
v___x_381_ = lean_io_getenv(v___x_380_);
if (lean_obj_tag(v___x_381_) == 1)
{
lean_object* v_val_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_463_; 
v_val_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_463_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_463_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_val_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_463_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; 
lean_inc(v_val_382_);
v___x_386_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_382_);
if (lean_obj_tag(v___x_386_) == 1)
{
lean_object* v_val_387_; 
lean_del_object(v___x_384_);
v_val_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_386_, 1);
if (lean_obj_tag(v_val_387_) == 0)
{
lean_object* v_p_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_431_; 
v_p_388_ = lean_ctor_get(v_val_387_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_val_387_);
if (v_isSharedCheck_431_ == 0)
{
v___x_390_ = v_val_387_;
v_isShared_391_ = v_isSharedCheck_431_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_p_388_);
lean_dec(v_val_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_431_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_string_utf8_byte_size(v_p_388_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_dec_le(v___x_423_, v___x_422_);
if (v___x_424_ == 0)
{
lean_del_object(v___x_390_);
goto v___jp_392_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_string_memcmp(v_p_388_, v___x_425_, v___x_426_, v___x_426_, v___x_423_);
if (v___x_427_ == 0)
{
lean_del_object(v___x_390_);
goto v___jp_392_;
}
else
{
lean_object* v___x_429_; 
lean_dec(v_val_382_);
if (v_isShared_391_ == 0)
{
v___x_429_ = v___x_390_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_p_388_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
v___jp_392_:
{
lean_object* v___x_393_; 
lean_inc_ref(v_p_388_);
v___x_393_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_378_, v_p_388_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_413_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_413_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_413_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_413_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
if (lean_obj_tag(v_a_394_) == 1)
{
lean_object* v_val_398_; lean_object* v___x_400_; 
lean_dec_ref(v_p_388_);
lean_dec(v_val_382_);
v_val_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v_a_394_, 1);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_val_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_val_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v_a_394_);
v___x_402_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_403_ = lean_string_append(v___x_402_, v_val_382_);
lean_dec(v_val_382_);
v___x_404_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2));
v___x_405_ = lean_string_append(v___x_403_, v___x_404_);
v___x_406_ = lean_string_append(v___x_405_, v_p_388_);
lean_dec_ref(v_p_388_);
v___x_407_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3));
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
v___x_409_ = lean_mk_io_user_error(v___x_408_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 1);
lean_ctor_set(v___x_396_, 0, v___x_409_);
v___x_411_ = v___x_396_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_p_388_);
lean_dec(v_val_382_);
v_a_414_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_393_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_393_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
else
{
lean_object* v_id_432_; lean_object* v___x_433_; 
v_id_432_ = lean_ctor_get(v_val_387_, 0);
lean_inc_ref(v_id_432_);
lean_dec_ref_known(v_val_387_, 1);
v___x_433_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_378_, v_id_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_450_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_450_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_450_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
if (lean_obj_tag(v_a_434_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_440_; 
lean_dec(v_val_382_);
v_val_438_ = lean_ctor_get(v_a_434_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_a_434_, 1);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v_val_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_val_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec(v_a_434_);
v___x_442_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_443_ = lean_string_append(v___x_442_, v_val_382_);
lean_dec(v_val_382_);
v___x_444_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__4));
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
v___x_446_ = lean_mk_io_user_error(v___x_445_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 1);
lean_ctor_set(v___x_436_, 0, v___x_446_);
v___x_448_ = v___x_436_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_val_382_);
v_a_451_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_433_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_433_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v___x_386_);
lean_dec(v_val_382_);
v___x_459_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 0);
lean_ctor_set(v___x_384_, 0, v___x_459_);
v___x_461_ = v___x_384_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_381_);
v___x_464_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object* v_zonesPaths_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_466_);
lean_dec_ref(v_zonesPaths_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object* v_db_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0));
v___x_489_ = lean_io_getenv(v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_db_486_);
return v___x_490_;
}
else
{
lean_object* v_val_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_511_; 
v_val_491_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_511_ == 0)
{
v___x_493_ = v___x_489_;
v_isShared_494_ = v_isSharedCheck_511_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_val_491_);
lean_dec(v___x_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_511_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1));
v___x_496_ = lean_string_dec_eq(v_val_491_, v___x_495_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
v___x_497_ = l_System_FilePath_pathExists(v_val_491_);
if (v___x_497_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_val_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 0);
lean_ctor_set(v___x_493_, 0, v_db_486_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_db_486_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_mk_empty_array_with_capacity(v___x_501_);
v___x_503_ = lean_array_push(v___x_502_, v_val_491_);
v___x_504_ = l_Array_append___redArg(v___x_503_, v_db_486_);
lean_dec_ref(v_db_486_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 0);
lean_ctor_set(v___x_493_, 0, v___x_504_);
v___x_506_ = v___x_493_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v___x_509_; 
lean_dec(v_val_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 0);
lean_ctor_set(v___x_493_, 0, v_db_486_);
v___x_509_ = v___x_493_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_db_486_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object* v_db_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object* v_db_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_a_518_; lean_object* v___x_519_; 
v___x_517_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_515_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v___x_519_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_518_);
lean_dec(v_a_518_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Std_Time_Database_TZdb_localRules(v_a_520_);
return v___x_521_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_519_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_519_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object* v_db_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object* v_id_536_, lean_object* v_as_537_, size_t v_sz_538_, size_t v_i_539_, lean_object* v_b_540_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_dec_ref(v_id_536_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_b_540_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
lean_dec_ref(v_b_540_);
v___x_544_ = lean_box(0);
v___x_545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_a_546_ = lean_array_uget_borrowed(v_as_537_, v_i_539_);
lean_inc_ref(v_id_536_);
lean_inc(v_a_546_);
v___x_547_ = l_System_FilePath_join(v_a_546_, v_id_536_);
v___x_548_ = l_System_FilePath_pathExists(v___x_547_);
lean_dec_ref(v___x_547_);
if (v___x_548_ == 0)
{
size_t v___x_549_; size_t v___x_550_; 
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_539_, v___x_549_);
v_i_539_ = v___x_550_;
v_b_540_ = v___x_545_;
goto _start;
}
else
{
lean_object* v___x_552_; 
lean_inc(v_a_546_);
v___x_552_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_546_, v_id_536_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_a_553_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_544_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_552_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_552_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object* v_id_571_, lean_object* v_as_572_, lean_object* v_sz_573_, lean_object* v_i_574_, lean_object* v_b_575_, lean_object* v___y_576_){
_start:
{
size_t v_sz_boxed_577_; size_t v_i_boxed_578_; lean_object* v_res_579_; 
v_sz_boxed_577_ = lean_unbox_usize(v_sz_573_);
lean_dec(v_sz_573_);
v_i_boxed_578_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_571_, v_as_572_, v_sz_boxed_577_, v_i_boxed_578_, v_b_575_);
lean_dec_ref(v_as_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object* v_db_582_, lean_object* v_id_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v___x_590_; 
v___x_585_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_582_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref(v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_sz_588_ = lean_array_size(v_a_586_);
v___x_589_ = ((size_t)0ULL);
lean_inc_ref(v_id_583_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_583_, v_a_586_, v_sz_588_, v___x_589_, v___x_587_);
lean_dec(v_a_586_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_608_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_608_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_608_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_608_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_fst_595_; 
v_fst_595_ = lean_ctor_get(v_a_591_, 0);
lean_inc(v_fst_595_);
lean_dec(v_a_591_);
if (lean_obj_tag(v_fst_595_) == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_596_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__0));
v___x_597_ = lean_string_append(v___x_596_, v_id_583_);
lean_dec_ref(v_id_583_);
v___x_598_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__1));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = lean_mk_io_user_error(v___x_599_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 1);
lean_ctor_set(v___x_593_, 0, v___x_600_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
lean_object* v_val_604_; lean_object* v___x_606_; 
lean_dec_ref(v_id_583_);
v_val_604_ = lean_ctor_get(v_fst_595_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_fst_595_, 1);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_val_604_);
v___x_606_ = v___x_593_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_val_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_id_583_);
v_a_609_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_590_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_590_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object* v_db_617_, lean_object* v_id_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_617_, v_id_618_);
return v_res_620_;
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

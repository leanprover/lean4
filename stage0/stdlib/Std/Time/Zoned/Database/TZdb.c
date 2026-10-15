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
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_tag_nat(v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl___boxed(lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_Time_Database_TZdb_TZSpec_ctorIdx___impl(v_x_176_);
lean_dec_ref(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(lean_object* v_t_178_, lean_object* v_k_179_){
_start:
{
lean_object* v_p_180_; lean_object* v___x_181_; 
v_p_180_ = lean_ctor_get(v_t_178_, 0);
lean_inc_ref(v_p_180_);
lean_dec_ref(v_t_178_);
v___x_181_ = lean_apply_1(v_k_179_, v_p_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_184_, v_k_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_ctorElim___boxed(lean_object* v_motive_188_, lean_object* v_ctorIdx_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_k_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim(v_motive_188_, v_ctorIdx_189_, v_t_190_, v_h_191_, v_k_192_);
lean_dec(v_ctorIdx_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim___redArg(lean_object* v_t_194_, lean_object* v_filePath_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_194_, v_filePath_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_filePath_elim(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_filePath_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_198_, v_filePath_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim___redArg(lean_object* v_t_202_, lean_object* v_zoneId_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_202_, v_zoneId_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_TZSpec_zoneId_elim(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_zoneId_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_206_, v_zoneId_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(2u);
v___x_217_ = lean_nat_to_int(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_to_int(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr(lean_object* v_x_226_, lean_object* v_prec_227_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_p_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_248_; 
v_p_228_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_248_ == 0)
{
v___x_230_ = v_x_226_;
v_isShared_231_ = v_isSharedCheck_248_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_p_228_);
lean_dec(v_x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_248_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___y_233_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1024u);
v___x_245_ = lean_nat_dec_le(v___x_244_, v_prec_227_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_233_ = v___x_246_;
goto v___jp_232_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_233_ = v___x_247_;
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2));
v___x_235_ = l_String_quote(v_p_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 3);
lean_ctor_set(v___x_230_, 0, v___x_235_);
v___x_237_ = v___x_230_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_243_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_234_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
lean_inc(v___y_233_);
v___x_239_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_239_, 0, v___y_233_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = 0;
v___x_241_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*1, v___x_240_);
v___x_242_ = l_Repr_addAppParen(v___x_241_, v_prec_227_);
return v___x_242_;
}
}
}
}
else
{
lean_object* v_id_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_269_; 
v_id_249_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_269_ == 0)
{
v___x_251_ = v_x_226_;
v_isShared_252_ = v_isSharedCheck_269_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_id_249_);
lean_dec(v_x_226_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_269_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___y_254_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(1024u);
v___x_266_ = lean_nat_dec_le(v___x_265_, v_prec_227_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3);
v___y_254_ = v___x_267_;
goto v___jp_253_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4, &l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once, _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4);
v___y_254_ = v___x_268_;
goto v___jp_253_;
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = ((lean_object*)(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7));
v___x_256_ = l_String_quote(v_id_249_);
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 3);
lean_ctor_set(v___x_251_, 0, v___x_256_);
v___x_258_ = v___x_251_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_264_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_255_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
lean_inc(v___y_254_);
v___x_260_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_260_, 0, v___y_254_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = 0;
v___x_262_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_261_);
v___x_263_ = l_Repr_addAppParen(v___x_262_, v_prec_227_);
return v___x_263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed(lean_object* v_x_270_, lean_object* v_prec_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr(v_x_270_, v_prec_271_);
lean_dec(v_prec_271_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Database_TZdb_instBEqTZSpec_beq(lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v_p_277_; lean_object* v_p_278_; uint8_t v___x_279_; 
v_p_277_ = lean_ctor_get(v_x_275_, 0);
v_p_278_ = lean_ctor_get(v_x_276_, 0);
v___x_279_ = lean_string_dec_eq(v_p_277_, v_p_278_);
return v___x_279_;
}
else
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
}
else
{
if (lean_obj_tag(v_x_276_) == 1)
{
lean_object* v_id_281_; lean_object* v_id_282_; uint8_t v___x_283_; 
v_id_281_ = lean_ctor_get(v_x_275_, 0);
v_id_282_ = lean_ctor_get(v_x_276_, 0);
v___x_283_ = lean_string_dec_eq(v_id_281_, v_id_282_);
return v___x_283_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_Time_Database_TZdb_instBEqTZSpec_beq(v_x_285_, v_x_286_);
lean_dec_ref(v_x_286_);
lean_dec_ref(v_x_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZValue(lean_object* v_tz_292_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_string_utf8_byte_size(v_tz_292_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_dec_le(v___x_301_, v___x_300_);
if (v___x_302_ == 0)
{
goto v___jp_293_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZValue___closed__0));
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_string_memcmp(v_tz_292_, v___x_303_, v___x_304_, v___x_304_, v___x_301_);
if (v___x_305_ == 0)
{
goto v___jp_293_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_p_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
lean_inc_ref(v_tz_292_);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v_tz_292_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_300_);
v___x_307_ = l_String_Slice_Pos_nextn(v___x_306_, v___x_304_, v___x_301_);
lean_dec_ref_known(v___x_306_, 3);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v_tz_292_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
lean_ctor_set(v___x_308_, 2, v___x_300_);
v_p_309_ = l_String_Slice_toString(v___x_308_);
lean_dec_ref_known(v___x_308_, 3);
v___x_310_ = lean_string_utf8_byte_size(v_p_309_);
v___x_311_ = lean_nat_dec_eq(v___x_310_, v___x_304_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_p_309_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v_p_309_);
v___x_314_ = lean_box(0);
return v___x_314_;
}
}
}
v___jp_293_:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_string_utf8_byte_size(v_tz_292_);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_tz_292_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
lean_dec_ref(v_tz_292_);
v___x_299_ = lean_box(0);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(lean_object* v_rel_318_, lean_object* v_as_319_, size_t v_sz_320_, size_t v_i_321_, lean_object* v_b_322_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_lt(v_i_321_, v_sz_320_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec_ref(v_rel_318_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_322_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
lean_dec_ref(v_b_322_);
v___x_326_ = lean_box(0);
v___x_327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_a_328_ = lean_array_uget_borrowed(v_as_319_, v_i_321_);
lean_inc_ref(v_rel_318_);
lean_inc(v_a_328_);
v___x_329_ = l_System_FilePath_join(v_a_328_, v_rel_318_);
v___x_330_ = l_System_FilePath_pathExists(v___x_329_);
if (v___x_330_ == 0)
{
size_t v___x_331_; size_t v___x_332_; 
lean_dec_ref(v___x_329_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_321_, v___x_331_);
v_i_321_ = v___x_332_;
v_b_322_ = v___x_327_;
goto _start;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_rel_318_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_329_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_326_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(lean_object* v_rel_338_, lean_object* v_as_339_, lean_object* v_sz_340_, lean_object* v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_){
_start:
{
size_t v_sz_boxed_344_; size_t v_i_boxed_345_; lean_object* v_res_346_; 
v_sz_boxed_344_ = lean_unbox_usize(v_sz_340_);
lean_dec(v_sz_340_);
v_i_boxed_345_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_338_, v_as_339_, v_sz_boxed_344_, v_i_boxed_345_, v_b_342_);
lean_dec_ref(v_as_339_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths(lean_object* v_searchPaths_347_, lean_object* v_rel_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; size_t v_sz_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_350_ = lean_box(0);
v___x_351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0));
v_sz_352_ = lean_array_size(v_searchPaths_347_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_348_, v_searchPaths_347_, v_sz_352_, v___x_353_, v___x_351_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_367_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_367_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_fst_359_; 
v_fst_359_ = lean_ctor_get(v_a_355_, 0);
lean_inc(v_fst_359_);
lean_dec(v_a_355_);
if (lean_obj_tag(v_fst_359_) == 0)
{
lean_object* v___x_361_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_350_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_350_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v_val_363_; lean_object* v___x_365_; 
v_val_363_ = lean_ctor_get(v_fst_359_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_fst_359_, 1);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_val_363_);
v___x_365_ = v___x_357_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_val_363_);
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
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_a_368_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_354_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_354_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_findInPaths___boxed(lean_object* v_searchPaths_376_, lean_object* v_rel_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_376_, v_rel_377_);
lean_dec_ref(v_searchPaths_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath(lean_object* v_zonesPaths_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0));
v___x_389_ = lean_io_getenv(v___x_388_);
if (lean_obj_tag(v___x_389_) == 1)
{
lean_object* v_val_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_471_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_471_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_471_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_val_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_471_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; 
lean_inc(v_val_390_);
v___x_394_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_390_);
if (lean_obj_tag(v___x_394_) == 1)
{
lean_object* v_val_395_; 
lean_del_object(v___x_392_);
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_394_, 1);
if (lean_obj_tag(v_val_395_) == 0)
{
lean_object* v_p_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_439_; 
v_p_396_ = lean_ctor_get(v_val_395_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_val_395_);
if (v_isSharedCheck_439_ == 0)
{
v___x_398_ = v_val_395_;
v_isShared_399_ = v_isSharedCheck_439_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_p_396_);
lean_dec(v_val_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_439_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = lean_string_utf8_byte_size(v_p_396_);
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_dec_le(v___x_431_, v___x_430_);
if (v___x_432_ == 0)
{
lean_del_object(v___x_398_);
goto v___jp_400_;
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_string_memcmp(v_p_396_, v___x_433_, v___x_434_, v___x_434_, v___x_431_);
if (v___x_435_ == 0)
{
lean_del_object(v___x_398_);
goto v___jp_400_;
}
else
{
lean_object* v___x_437_; 
lean_dec(v_val_390_);
if (v_isShared_399_ == 0)
{
v___x_437_ = v___x_398_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_p_396_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
v___jp_400_:
{
lean_object* v___x_401_; 
lean_inc_ref(v_p_396_);
v___x_401_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_386_, v_p_396_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_421_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_421_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_421_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_421_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
if (lean_obj_tag(v_a_402_) == 1)
{
lean_object* v_val_406_; lean_object* v___x_408_; 
lean_dec_ref(v_p_396_);
lean_dec(v_val_390_);
v_val_406_ = lean_ctor_get(v_a_402_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_a_402_, 1);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_val_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_val_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_a_402_);
v___x_410_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_411_ = lean_string_append(v___x_410_, v_val_390_);
lean_dec(v_val_390_);
v___x_412_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
v___x_414_ = lean_string_append(v___x_413_, v_p_396_);
lean_dec_ref(v_p_396_);
v___x_415_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3));
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
v___x_417_ = lean_mk_io_user_error(v___x_416_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_417_);
v___x_419_ = v___x_404_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
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
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_p_396_);
lean_dec(v_val_390_);
v_a_422_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_401_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_401_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
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
}
}
else
{
lean_object* v_id_440_; lean_object* v___x_441_; 
v_id_440_ = lean_ctor_get(v_val_395_, 0);
lean_inc_ref(v_id_440_);
lean_dec_ref_known(v_val_395_, 1);
v___x_441_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_386_, v_id_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_458_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
if (lean_obj_tag(v_a_442_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_448_; 
lean_dec(v_val_390_);
v_val_446_ = lean_ctor_get(v_a_442_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_a_442_, 1);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_val_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_val_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec(v_a_442_);
v___x_450_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1));
v___x_451_ = lean_string_append(v___x_450_, v_val_390_);
lean_dec(v_val_390_);
v___x_452_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__4));
v___x_453_ = lean_string_append(v___x_451_, v___x_452_);
v___x_454_ = lean_mk_io_user_error(v___x_453_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v___x_454_);
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
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
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_val_390_);
v_a_459_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_441_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_441_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
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
}
else
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec(v___x_394_);
lean_dec(v_val_390_);
v___x_467_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 0);
lean_ctor_set(v___x_392_, 0, v___x_467_);
v___x_469_ = v___x_392_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v___x_389_);
v___x_472_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5));
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveLocalPath___boxed(lean_object* v_zonesPaths_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_474_);
lean_dec_ref(v_zonesPaths_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths(lean_object* v_db_494_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0));
v___x_497_ = lean_io_getenv(v___x_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_db_494_);
return v___x_498_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_519_; 
v_val_499_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_519_ == 0)
{
v___x_501_ = v___x_497_;
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_val_499_);
lean_dec(v___x_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1));
v___x_504_ = lean_string_dec_eq(v_val_499_, v___x_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = l_System_FilePath_pathExists(v_val_499_);
if (v___x_505_ == 0)
{
lean_object* v___x_507_; 
lean_dec(v_val_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 0);
lean_ctor_set(v___x_501_, 0, v_db_494_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_db_494_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_mk_empty_array_with_capacity(v___x_509_);
v___x_511_ = lean_array_push(v___x_510_, v_val_499_);
v___x_512_ = l_Array_append___redArg(v___x_511_, v_db_494_);
lean_dec_ref(v_db_494_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 0);
lean_ctor_set(v___x_501_, 0, v___x_512_);
v___x_514_ = v___x_501_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v_val_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 0);
lean_ctor_set(v___x_501_, 0, v_db_494_);
v___x_517_ = v___x_501_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_db_494_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(lean_object* v_db_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules(lean_object* v_db_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_527_; 
v___x_525_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_523_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_526_);
lean_dec(v_a_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = l_Std_Time_Database_TZdb_localRules(v_a_528_);
return v___x_529_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_527_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_527_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(lean_object* v_db_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(lean_object* v_id_544_, lean_object* v_as_545_, size_t v_sz_546_, size_t v_i_547_, lean_object* v_b_548_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_547_, v_sz_546_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v_id_544_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_b_548_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
lean_dec_ref(v_b_548_);
v___x_552_ = lean_box(0);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_a_554_ = lean_array_uget_borrowed(v_as_545_, v_i_547_);
lean_inc_ref(v_id_544_);
lean_inc(v_a_554_);
v___x_555_ = l_System_FilePath_join(v_a_554_, v_id_544_);
v___x_556_ = l_System_FilePath_pathExists(v___x_555_);
lean_dec_ref(v___x_555_);
if (v___x_556_ == 0)
{
size_t v___x_557_; size_t v___x_558_; 
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_547_, v___x_557_);
v_i_547_ = v___x_558_;
v_b_548_ = v___x_553_;
goto _start;
}
else
{
lean_object* v___x_560_; 
lean_inc(v_a_554_);
v___x_560_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_554_, v_id_544_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_a_561_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_552_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_566_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_a_571_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_560_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_560_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(lean_object* v_id_579_, lean_object* v_as_580_, lean_object* v_sz_581_, lean_object* v_i_582_, lean_object* v_b_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_581_);
lean_dec(v_sz_581_);
v_i_boxed_586_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_579_, v_as_580_, v_sz_boxed_585_, v_i_boxed_586_, v_b_583_);
lean_dec_ref(v_as_580_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules(lean_object* v_db_590_, lean_object* v_id_591_){
_start:
{
lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_593_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_590_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0));
v_sz_596_ = lean_array_size(v_a_594_);
v___x_597_ = ((size_t)0ULL);
lean_inc_ref(v_id_591_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_591_, v_a_594_, v_sz_596_, v___x_597_, v___x_595_);
lean_dec(v_a_594_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_616_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_616_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_616_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_616_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_fst_603_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
lean_inc(v_fst_603_);
lean_dec(v_a_599_);
if (lean_obj_tag(v_fst_603_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_604_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__0));
v___x_605_ = lean_string_append(v___x_604_, v_id_591_);
lean_dec_ref(v_id_591_);
v___x_606_ = ((lean_object*)(l_Std_Time_Database_TZdb_getZoneRules___closed__1));
v___x_607_ = lean_string_append(v___x_605_, v___x_606_);
v___x_608_ = lean_mk_io_user_error(v___x_607_);
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 1);
lean_ctor_set(v___x_601_, 0, v___x_608_);
v___x_610_ = v___x_601_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
lean_object* v_val_612_; lean_object* v___x_614_; 
lean_dec_ref(v_id_591_);
v_val_612_ = lean_ctor_get(v_fst_603_, 0);
lean_inc(v_val_612_);
lean_dec_ref_known(v_fst_603_, 1);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_val_612_);
v___x_614_ = v___x_601_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_val_612_);
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
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_id_591_);
v_a_617_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_598_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_598_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_getZoneRules___boxed(lean_object* v_db_625_, lean_object* v_id_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_625_, v_id_626_);
return v_res_628_;
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

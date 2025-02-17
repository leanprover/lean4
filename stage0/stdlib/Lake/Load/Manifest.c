// Lean compiler output
// Module: Lake.Load.Manifest
// Imports: Lake.Util.Log Lake.Util.Name Lake.Util.FilePath Lake.Util.JsonObject Lake.Util.Version Lake.Config.Defaults
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
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__42;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
static lean_object* l_Lake_Manifest_version___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__27;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__46;
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__33;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__5;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__31;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
lean_object* l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instToJson;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__6;
static lean_object* l_Lake_PackageEntry_toJson___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__2;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__8;
static lean_object* l_Lake_Manifest_toJson___closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__12;
static lean_object* l_Lake_Manifest_toJson___closed__7;
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__6;
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__30;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
static lean_object* l_Lake_PackageEntry_instFromJson___closed__1;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_instInhabitedPackageEntryV6___closed__1;
uint8_t l_Ord_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
static lean_object* l_Lake_Manifest_parse___closed__1;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__37;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__39;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
static lean_object* l_Lake_PackageEntry_toJson___closed__6;
static lean_object* l_Lake_Manifest_getPackages___closed__2;
static lean_object* l_Lake_Manifest_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedJson;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
static lean_object* l_Lake_Manifest_toJson___closed__3;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
static lean_object* l_Lake_Manifest_saveEntries___closed__1;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__2;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__1;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__47;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_version___closed__1;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__5;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__41;
static lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__38;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__9;
static lean_object* l_Lake_Manifest_getPackages___closed__8;
static lean_object* l_Lake_instInhabitedPackageEntrySrc___closed__1;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__6;
static lean_object* l_Lake_Manifest_toJson___closed__5;
LEAN_EXPORT lean_object* l_Lake_Manifest_instFromJson;
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__45;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__32;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
static lean_object* l_Lake_PackageEntry_toJson___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__4;
static lean_object* l_Lake_Manifest_parse___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__18;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__10;
static lean_object* l_Lake_PackageEntry_toJson___closed__9;
static lean_object* l_Lake_Manifest_getPackages___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12;
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__14;
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__28;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instFromJson;
static lean_object* l_Lake_PackageEntry_toJson___closed__5;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__22;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__19;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__4;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__23;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__34;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__2;
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___lambda__1(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__8;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lake_instToJsonPackageEntryV6;
static lean_object* l_Lake_Manifest_getPackages___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___boxed(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
static lean_object* l_Lake_instInhabitedPackageEntry___closed__1;
static lean_object* l_Lake_Manifest_toJson___closed__8;
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3(size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_instToJson;
static lean_object* l_Lake_PackageEntry_toJson___closed__10;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__1;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__24;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__12;
static lean_object* l_Lake_PackageEntry_toJson___closed__7;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__29;
static lean_object* l_Lake_Manifest_getVersion___closed__7;
lean_object* l_Lake_StdVer_parse(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__4;
static lean_object* l_Lake_PackageEntry_toJson___closed__11;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__8;
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__4;
LEAN_EXPORT lean_object* l_Lake_instFromJsonPackageEntryV6;
extern lean_object* l_Lake_instOrdStdVer;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object*);
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__3;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_(lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__13;
static lean_object* l_Lake_instToJsonPackageEntryV6___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__25;
static lean_object* l_Lake_Manifest_getVersion___closed__5;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11;
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_Manifest_version___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__40;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Manifest_instFromJson___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__17;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__35;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Manifest_version;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__15;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
static lean_object* l_Lake_Manifest_toJson___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__44;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Manifest_getVersion___closed__2;
size_t lean_array_size(lean_object*);
static size_t l_Lake_Manifest_getPackages___closed__4;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__43;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__4;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
extern lean_object* l_Lake_defaultConfigFile;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__6;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__16;
static lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__2;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntryV6;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__36;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__4;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__26;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6;
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__21;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_instFromJsonPackageEntryV6___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__13;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__6;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__5;
static lean_object* l_Lake_Manifest_getVersion___closed__1;
static lean_object* _init_l_Lake_Manifest_version___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_version___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_version___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__1;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_version() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Manifest_version___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected name", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_String_toName(x_5);
x_14 = l_Lean_Name_isAnonymous(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_12, x_13, x_19);
x_1 = x_20;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_22 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__2;
return x_22;
}
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev\?", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir\?", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__8;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__6;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__4;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_mk(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
x_21 = lean_unsigned_to_nat(7u);
x_22 = l_Lean_Json_parseTagged(x_5, x_20, x_21, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_25 = l_Except_orElseLazy___rarg(x_22, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_29 = l_Except_orElseLazy___rarg(x_27, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_187 = l_Lean_instInhabitedJson;
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_array_get(x_187, x_30, x_188);
lean_inc(x_189);
x_190 = l_Lean_Json_getStr_x3f(x_189);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
lean_dec(x_189);
lean_dec(x_30);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_193 = l_Except_orElseLazy___rarg(x_190, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
lean_dec(x_190);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_197 = l_Except_orElseLazy___rarg(x_195, x_196);
return x_197;
}
}
else
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_190);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = lean_ctor_get(x_190, 0);
x_200 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_201 = lean_string_dec_eq(x_199, x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_String_toName(x_199);
x_203 = l_Lean_Name_isAnonymous(x_202);
if (x_203 == 0)
{
lean_free_object(x_190);
lean_dec(x_189);
x_31 = x_202;
goto block_186;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_202);
lean_dec(x_30);
x_204 = lean_unsigned_to_nat(80u);
x_205 = l_Lean_Json_pretty(x_189, x_204);
x_206 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_207 = lean_string_append(x_206, x_205);
lean_dec(x_205);
x_208 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_209 = lean_string_append(x_207, x_208);
lean_ctor_set_tag(x_190, 0);
lean_ctor_set(x_190, 0, x_209);
x_210 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_211 = l_Except_orElseLazy___rarg(x_190, x_210);
return x_211;
}
}
else
{
lean_object* x_212; 
lean_free_object(x_190);
lean_dec(x_199);
lean_dec(x_189);
x_212 = lean_box(0);
x_31 = x_212;
goto block_186;
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_213 = lean_ctor_get(x_190, 0);
lean_inc(x_213);
lean_dec(x_190);
x_214 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_215 = lean_string_dec_eq(x_213, x_214);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = l_String_toName(x_213);
x_217 = l_Lean_Name_isAnonymous(x_216);
if (x_217 == 0)
{
lean_dec(x_189);
x_31 = x_216;
goto block_186;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_216);
lean_dec(x_30);
x_218 = lean_unsigned_to_nat(80u);
x_219 = l_Lean_Json_pretty(x_189, x_218);
x_220 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_221 = lean_string_append(x_220, x_219);
lean_dec(x_219);
x_222 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_226 = l_Except_orElseLazy___rarg(x_224, x_225);
return x_226;
}
}
else
{
lean_object* x_227; 
lean_dec(x_213);
lean_dec(x_189);
x_227 = lean_box(0);
x_31 = x_227;
goto block_186;
}
}
}
block_186:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_instInhabitedJson;
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_array_get(x_32, x_30, x_33);
x_35 = l_Lean_Json_getObj_x3f(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_31);
lean_dec(x_30);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_38 = l_Except_orElseLazy___rarg(x_35, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_42 = l_Except_orElseLazy___rarg(x_40, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_box(0);
x_45 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(x_44, x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_31);
lean_dec(x_30);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_48 = l_Except_orElseLazy___rarg(x_45, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_52 = l_Except_orElseLazy___rarg(x_50, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_array_get(x_32, x_30, x_54);
x_56 = l_Lean_Json_getBool_x3f(x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_30);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_59 = l_Except_orElseLazy___rarg(x_56, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_63 = l_Except_orElseLazy___rarg(x_61, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_unsigned_to_nat(3u);
x_66 = lean_array_get(x_32, x_30, x_65);
x_67 = l_Lean_Json_getStr_x3f(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_30);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_70 = l_Except_orElseLazy___rarg(x_67, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_74 = l_Except_orElseLazy___rarg(x_72, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_unsigned_to_nat(4u);
x_77 = lean_array_get(x_32, x_30, x_76);
x_78 = l_Lean_Json_getStr_x3f(x_77);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_30);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_81 = l_Except_orElseLazy___rarg(x_78, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_85 = l_Except_orElseLazy___rarg(x_83, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_155; lean_object* x_156; 
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
x_155 = lean_unsigned_to_nat(5u);
x_156 = lean_array_get(x_32, x_30, x_155);
switch (lean_obj_tag(x_156)) {
case 0:
{
lean_object* x_157; 
x_157 = lean_box(0);
x_88 = x_157;
goto block_154;
}
case 1:
{
lean_object* x_158; 
x_158 = l_Lean_Json_getStr_x3f(x_156);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_161 = l_Except_orElseLazy___rarg(x_158, x_160);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
lean_dec(x_158);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_165 = l_Except_orElseLazy___rarg(x_163, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_158, 0);
lean_inc(x_166);
lean_dec(x_158);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_88 = x_167;
goto block_154;
}
}
default: 
{
lean_object* x_168; uint8_t x_169; 
lean_inc(x_156);
x_168 = l_Lean_Json_getStr_x3f(x_156);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_171; 
lean_free_object(x_156);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_30);
x_171 = !lean_is_exclusive(x_168);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_173 = l_Except_orElseLazy___rarg(x_168, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
lean_dec(x_168);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_177 = l_Except_orElseLazy___rarg(x_175, x_176);
return x_177;
}
}
else
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_168, 0);
lean_inc(x_178);
lean_dec(x_168);
lean_ctor_set_tag(x_156, 1);
lean_ctor_set(x_156, 0, x_178);
x_88 = x_156;
goto block_154;
}
}
else
{
lean_dec(x_156);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_30);
x_179 = lean_ctor_get(x_168, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_180 = x_168;
} else {
 lean_dec_ref(x_168);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
x_182 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_183 = l_Except_orElseLazy___rarg(x_181, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_168, 0);
lean_inc(x_184);
lean_dec(x_168);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_88 = x_185;
goto block_154;
}
}
}
}
block_154:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_unsigned_to_nat(6u);
x_90 = lean_array_get(x_32, x_30, x_89);
lean_dec(x_30);
switch (lean_obj_tag(x_90)) {
case 0:
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_53);
lean_ctor_set(x_92, 2, x_75);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_88);
lean_ctor_set(x_92, 5, x_91);
x_93 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_93);
if (lean_is_scalar(x_87)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_87;
}
lean_ctor_set(x_94, 0, x_92);
x_95 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_96 = l_Except_orElseLazy___rarg(x_94, x_95);
return x_96;
}
case 1:
{
lean_object* x_97; 
lean_dec(x_87);
x_97 = l_Lean_Json_getStr_x3f(x_90);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_100 = l_Except_orElseLazy___rarg(x_97, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_104 = l_Except_orElseLazy___rarg(x_102, x_103);
return x_104;
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_97);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_97, 0);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_108, 0, x_31);
lean_ctor_set(x_108, 1, x_53);
lean_ctor_set(x_108, 2, x_75);
lean_ctor_set(x_108, 3, x_86);
lean_ctor_set(x_108, 4, x_88);
lean_ctor_set(x_108, 5, x_107);
x_109 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_108, sizeof(void*)*6, x_109);
lean_ctor_set(x_97, 0, x_108);
x_110 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_111 = l_Except_orElseLazy___rarg(x_97, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
lean_dec(x_97);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_114, 0, x_31);
lean_ctor_set(x_114, 1, x_53);
lean_ctor_set(x_114, 2, x_75);
lean_ctor_set(x_114, 3, x_86);
lean_ctor_set(x_114, 4, x_88);
lean_ctor_set(x_114, 5, x_113);
x_115 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_115);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_117 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_118 = l_Except_orElseLazy___rarg(x_116, x_117);
return x_118;
}
}
}
default: 
{
lean_object* x_119; uint8_t x_120; 
lean_dec(x_87);
lean_inc(x_90);
x_119 = l_Lean_Json_getStr_x3f(x_90);
x_120 = !lean_is_exclusive(x_90);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_90, 0);
lean_dec(x_121);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_122; 
lean_free_object(x_90);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_124 = l_Except_orElseLazy___rarg(x_119, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_119, 0);
lean_inc(x_125);
lean_dec(x_119);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_128 = l_Except_orElseLazy___rarg(x_126, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_119);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_119, 0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_130);
x_131 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_131, 0, x_31);
lean_ctor_set(x_131, 1, x_53);
lean_ctor_set(x_131, 2, x_75);
lean_ctor_set(x_131, 3, x_86);
lean_ctor_set(x_131, 4, x_88);
lean_ctor_set(x_131, 5, x_90);
x_132 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_131, sizeof(void*)*6, x_132);
lean_ctor_set(x_119, 0, x_131);
x_133 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_134 = l_Except_orElseLazy___rarg(x_119, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
lean_dec(x_119);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_135);
x_136 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_136, 0, x_31);
lean_ctor_set(x_136, 1, x_53);
lean_ctor_set(x_136, 2, x_75);
lean_ctor_set(x_136, 3, x_86);
lean_ctor_set(x_136, 4, x_88);
lean_ctor_set(x_136, 5, x_90);
x_137 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_136, sizeof(void*)*6, x_137);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_136);
x_139 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_140 = l_Except_orElseLazy___rarg(x_138, x_139);
return x_140;
}
}
}
else
{
lean_dec(x_90);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_31);
x_141 = lean_ctor_get(x_119, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_142 = x_119;
} else {
 lean_dec_ref(x_119);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 1, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_141);
x_144 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_145 = l_Except_orElseLazy___rarg(x_143, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_119, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_147 = x_119;
} else {
 lean_dec_ref(x_119);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_146);
x_149 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_149, 0, x_31);
lean_ctor_set(x_149, 1, x_53);
lean_ctor_set(x_149, 2, x_75);
lean_ctor_set(x_149, 3, x_86);
lean_ctor_set(x_149, 4, x_88);
lean_ctor_set(x_149, 5, x_148);
x_150 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_149, sizeof(void*)*6, x_150);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_149);
x_152 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10;
x_153 = l_Except_orElseLazy___rarg(x_151, x_152);
return x_153;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("opts", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inherited", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dir", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("path", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_box(0);
x_3 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14;
lean_inc(x_1);
x_6 = l_Lean_Json_parseTagged(x_1, x_3, x_4, x_5);
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6;
x_8 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4;
x_9 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2;
x_10 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___boxed), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Except_orElseLazy___rarg(x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Except_orElseLazy___rarg(x_14, x_10);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_64 = l_Lean_instInhabitedJson;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get(x_64, x_16, x_65);
lean_inc(x_66);
x_67 = l_Lean_Json_getStr_x3f(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_66);
lean_dec(x_16);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Except_orElseLazy___rarg(x_67, x_10);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Except_orElseLazy___rarg(x_71, x_10);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_76 = lean_string_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_String_toName(x_74);
x_78 = l_Lean_Name_isAnonymous(x_77);
if (x_78 == 0)
{
lean_free_object(x_67);
lean_dec(x_66);
x_17 = x_77;
goto block_63;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_77);
lean_dec(x_16);
x_79 = lean_unsigned_to_nat(80u);
x_80 = l_Lean_Json_pretty(x_66, x_79);
x_81 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_84 = lean_string_append(x_82, x_83);
lean_ctor_set_tag(x_67, 0);
lean_ctor_set(x_67, 0, x_84);
x_85 = l_Except_orElseLazy___rarg(x_67, x_10);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_free_object(x_67);
lean_dec(x_74);
lean_dec(x_66);
x_86 = lean_box(0);
x_17 = x_86;
goto block_63;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_67, 0);
lean_inc(x_87);
lean_dec(x_67);
x_88 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_89 = lean_string_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_String_toName(x_87);
x_91 = l_Lean_Name_isAnonymous(x_90);
if (x_91 == 0)
{
lean_dec(x_66);
x_17 = x_90;
goto block_63;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_90);
lean_dec(x_16);
x_92 = lean_unsigned_to_nat(80u);
x_93 = l_Lean_Json_pretty(x_66, x_92);
x_94 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Except_orElseLazy___rarg(x_98, x_10);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_87);
lean_dec(x_66);
x_100 = lean_box(0);
x_17 = x_100;
goto block_63;
}
}
}
block_63:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_instInhabitedJson;
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_array_get(x_18, x_16, x_19);
x_21 = l_Lean_Json_getObj_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Except_orElseLazy___rarg(x_21, x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Except_orElseLazy___rarg(x_25, x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Except_orElseLazy___rarg(x_29, x_10);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Except_orElseLazy___rarg(x_33, x_10);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_array_get(x_18, x_16, x_36);
x_38 = l_Lean_Json_getBool_x3f(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Except_orElseLazy___rarg(x_38, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Except_orElseLazy___rarg(x_42, x_10);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_array_get(x_18, x_16, x_45);
lean_dec(x_16);
x_47 = l_Lean_Json_getStr_x3f(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_44);
lean_dec(x_35);
lean_dec(x_17);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Except_orElseLazy___rarg(x_47, x_10);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Except_orElseLazy___rarg(x_51, x_10);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_unbox(x_44);
lean_dec(x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_56);
lean_ctor_set(x_47, 0, x_55);
x_57 = l_Except_orElseLazy___rarg(x_47, x_10);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
lean_dec(x_47);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_35);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_unbox(x_44);
lean_dec(x_44);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_60);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_62 = l_Except_orElseLazy___rarg(x_61, x_10);
return x_62;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_instFromJsonPackageEntryV6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonPackageEntryV6___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(x_1, x_2, x_4);
x_9 = 1;
lean_inc(x_1);
x_10 = l_Lean_Name_toString(x_5, x_9, x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_8, x_10, x_11);
x_2 = x_12;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(x_1, x_3);
x_8 = 1;
x_9 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_10 = l_Lean_Name_toString(x_4, x_8, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_7, x_10, x_11);
x_1 = x_12;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(x_1, x_2, x_4);
x_9 = 1;
lean_inc(x_1);
x_10 = l_Lean_Name_toString(x_5, x_9, x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_8, x_10, x_11);
x_2 = x_12;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(x_1, x_3);
x_8 = 1;
x_9 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_10 = l_Lean_Name_toString(x_4, x_8, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_7, x_10, x_11);
x_1 = x_12;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 1;
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_8 = l_Lean_Name_toString(x_2, x_6, x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_4);
x_14 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_mkRelPathString(x_5);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(x_12, x_3);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Json_mkObj(x_28);
x_30 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 5);
lean_inc(x_40);
lean_dec(x_1);
x_41 = 1;
x_42 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_43 = l_Lean_Name_toString(x_34, x_41, x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_48, 0, x_36);
x_49 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_37);
x_52 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_38);
x_55 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(x_47, x_35);
x_59 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_62 = x_112;
goto block_111;
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_39);
if (x_113 == 0)
{
lean_ctor_set_tag(x_39, 3);
x_62 = x_39;
goto block_111;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_39, 0);
lean_inc(x_114);
lean_dec(x_39);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_62 = x_115;
goto block_111;
}
}
block_111:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_50);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_46);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Json_mkObj(x_71);
x_73 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_76 = l_Lean_Json_mkObj(x_75);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_40);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_78 = lean_ctor_get(x_40, 0);
x_79 = l_Lake_mkRelPathString(x_78);
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 0, x_79);
x_80 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_40);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_57);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_56);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_53);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_50);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_61);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_46);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Json_mkObj(x_88);
x_90 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_57);
x_93 = l_Lean_Json_mkObj(x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_94 = lean_ctor_get(x_40, 0);
lean_inc(x_94);
lean_dec(x_40);
x_95 = l_Lake_mkRelPathString(x_94);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_57);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_64);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_56);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_53);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_50);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_61);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_46);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Json_mkObj(x_105);
x_107 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_110 = l_Lean_Json_mkObj(x_109);
return x_110;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonPackageEntryV6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonPackageEntryV6___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntryV6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lake_Manifest_version___closed__2;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntryV6___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntrySrc___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lake_Manifest_version___closed__2;
x_4 = 0;
x_5 = l_Lake_instInhabitedPackageEntrySrc___closed__1;
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntry___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scope", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configFile", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifestFile", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__5;
x_2 = l_Lake_PackageEntry_toJson___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__5;
x_2 = l_Lake_PackageEntry_toJson___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__9;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__11;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageEntry_toJson___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__10;
x_2 = l_Lake_PackageEntry_toJson___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_PackageEntry_toJson___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l_Lake_mkRelPathString(x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lake_PackageEntry_toJson___closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_20 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_20, 0, x_19);
x_21 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_1, 4);
lean_inc(x_25);
lean_dec(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_162; 
x_162 = lean_box(0);
x_26 = x_162;
goto block_161;
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_18);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_18, 0);
x_165 = l_Lake_mkRelPathString(x_164);
lean_ctor_set_tag(x_18, 3);
lean_ctor_set(x_18, 0, x_165);
x_26 = x_18;
goto block_161;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_18, 0);
lean_inc(x_166);
lean_dec(x_18);
x_167 = l_Lake_mkRelPathString(x_166);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_26 = x_168;
goto block_161;
}
}
block_161:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lake_PackageEntry_toJson___closed__3;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = l_Lake_mkRelPathString(x_34);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 0, x_35);
x_36 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
x_39 = l_List_appendTR___rarg(x_32, x_38);
x_40 = l_Lake_PackageEntry_toJson___closed__6;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_mkObj(x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
lean_dec(x_25);
x_44 = l_Lake_mkRelPathString(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_23);
x_49 = l_List_appendTR___rarg(x_32, x_48);
x_50 = l_Lake_PackageEntry_toJson___closed__6;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Json_mkObj(x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_25, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_25, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_25, 3);
lean_inc(x_56);
lean_dec(x_25);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_53);
x_58 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_54);
x_61 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
if (lean_obj_tag(x_55) == 0)
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = l_Lake_PackageEntry_toJson___closed__14;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_List_appendTR___rarg(x_32, x_65);
x_67 = l_Lake_PackageEntry_toJson___closed__8;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Json_mkObj(x_68);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_56, 0);
x_72 = l_Lake_mkRelPathString(x_71);
lean_ctor_set_tag(x_56, 3);
lean_ctor_set(x_56, 0, x_72);
x_73 = l_Lake_PackageEntry_toJson___closed__11;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_56);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_23);
x_76 = l_Lake_PackageEntry_toJson___closed__10;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_62);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_59);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_List_appendTR___rarg(x_32, x_79);
x_81 = l_Lake_PackageEntry_toJson___closed__8;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Json_mkObj(x_82);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = lean_ctor_get(x_56, 0);
lean_inc(x_84);
lean_dec(x_56);
x_85 = l_Lake_mkRelPathString(x_84);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lake_PackageEntry_toJson___closed__11;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_23);
x_90 = l_Lake_PackageEntry_toJson___closed__10;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_62);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_59);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_List_appendTR___rarg(x_32, x_93);
x_95 = l_Lake_PackageEntry_toJson___closed__8;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Lean_Json_mkObj(x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_55);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_ctor_set_tag(x_55, 3);
x_99 = l_Lake_PackageEntry_toJson___closed__9;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = l_Lake_PackageEntry_toJson___closed__13;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_62);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_59);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_List_appendTR___rarg(x_32, x_104);
x_106 = l_Lake_PackageEntry_toJson___closed__8;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Json_mkObj(x_107);
return x_108;
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_56);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_56, 0);
x_111 = l_Lake_mkRelPathString(x_110);
lean_ctor_set_tag(x_56, 3);
lean_ctor_set(x_56, 0, x_111);
x_112 = l_Lake_PackageEntry_toJson___closed__11;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_56);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_23);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_62);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_59);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_List_appendTR___rarg(x_32, x_117);
x_119 = l_Lake_PackageEntry_toJson___closed__8;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_Json_mkObj(x_120);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_122 = lean_ctor_get(x_56, 0);
lean_inc(x_122);
lean_dec(x_56);
x_123 = l_Lake_mkRelPathString(x_122);
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lake_PackageEntry_toJson___closed__11;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_23);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_100);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_62);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_59);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_List_appendTR___rarg(x_32, x_130);
x_132 = l_Lake_PackageEntry_toJson___closed__8;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Json_mkObj(x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_55, 0);
lean_inc(x_135);
lean_dec(x_55);
x_136 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_Lake_PackageEntry_toJson___closed__9;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = l_Lake_PackageEntry_toJson___closed__13;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_62);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_59);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_List_appendTR___rarg(x_32, x_142);
x_144 = l_Lake_PackageEntry_toJson___closed__8;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_Json_mkObj(x_145);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_147 = lean_ctor_get(x_56, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_148 = x_56;
} else {
 lean_dec_ref(x_56);
 x_148 = lean_box(0);
}
x_149 = l_Lake_mkRelPathString(x_147);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(3, 1, 0);
} else {
 x_150 = x_148;
 lean_ctor_set_tag(x_150, 3);
}
lean_ctor_set(x_150, 0, x_149);
x_151 = l_Lake_PackageEntry_toJson___closed__11;
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_23);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_138);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_62);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_59);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_List_appendTR___rarg(x_32, x_156);
x_158 = l_Lake_PackageEntry_toJson___closed__8;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = l_Lean_Json_mkObj(x_159);
return x_160;
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_PackageEntry_instToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_PackageEntry_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageEntry_instToJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package entry: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package entry '", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__7;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l_Lake_PackageEntry_toJson___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__12;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__14;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__16;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__19;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__21;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__23;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown package entry type '", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__26;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__29;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__31;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__32;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__34;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__36;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__37;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__39;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__41;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__42;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__43;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__44;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__46;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_9; 
x_9 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_Manifest_version___closed__2;
x_15 = lean_string_append(x_13, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_Manifest_version___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_308; lean_object* x_309; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_23 = x_9;
} else {
 lean_dec_ref(x_9);
 x_23 = lean_box(0);
}
x_308 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_309 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; 
lean_dec(x_23);
lean_dec(x_22);
x_310 = l_Lake_PackageEntry_fromJson_x3f___closed__45;
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_311);
x_312 = l_Lean_Json_getStr_x3f(x_311);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; 
lean_dec(x_311);
lean_dec(x_23);
lean_dec(x_22);
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_314 = lean_ctor_get(x_312, 0);
x_315 = l_Lake_PackageEntry_fromJson_x3f___closed__47;
x_316 = lean_string_append(x_315, x_314);
lean_dec(x_314);
x_317 = l_Lake_Manifest_version___closed__2;
x_318 = lean_string_append(x_316, x_317);
x_319 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_320 = lean_string_append(x_319, x_318);
lean_dec(x_318);
x_321 = lean_string_append(x_320, x_317);
lean_ctor_set(x_312, 0, x_321);
return x_312;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_312, 0);
lean_inc(x_322);
lean_dec(x_312);
x_323 = l_Lake_PackageEntry_fromJson_x3f___closed__47;
x_324 = lean_string_append(x_323, x_322);
lean_dec(x_322);
x_325 = l_Lake_Manifest_version___closed__2;
x_326 = lean_string_append(x_324, x_325);
x_327 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_328 = lean_string_append(x_327, x_326);
lean_dec(x_326);
x_329 = lean_string_append(x_328, x_325);
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
}
else
{
uint8_t x_331; 
x_331 = !lean_is_exclusive(x_312);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_332 = lean_ctor_get(x_312, 0);
x_333 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_334 = lean_string_dec_eq(x_332, x_333);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = l_String_toName(x_332);
x_336 = l_Lean_Name_isAnonymous(x_335);
if (x_336 == 0)
{
lean_free_object(x_312);
lean_dec(x_311);
x_24 = x_335;
goto block_307;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_335);
lean_dec(x_23);
lean_dec(x_22);
x_337 = lean_unsigned_to_nat(80u);
x_338 = l_Lean_Json_pretty(x_311, x_337);
x_339 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_340 = lean_string_append(x_339, x_338);
lean_dec(x_338);
x_341 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_342 = lean_string_append(x_340, x_341);
x_343 = l_Lake_PackageEntry_fromJson_x3f___closed__47;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_Lake_Manifest_version___closed__2;
x_346 = lean_string_append(x_344, x_345);
x_347 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_348 = lean_string_append(x_347, x_346);
lean_dec(x_346);
x_349 = lean_string_append(x_348, x_345);
lean_ctor_set_tag(x_312, 0);
lean_ctor_set(x_312, 0, x_349);
return x_312;
}
}
else
{
lean_object* x_350; 
lean_free_object(x_312);
lean_dec(x_332);
lean_dec(x_311);
x_350 = lean_box(0);
x_24 = x_350;
goto block_307;
}
}
else
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_351 = lean_ctor_get(x_312, 0);
lean_inc(x_351);
lean_dec(x_312);
x_352 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_353 = lean_string_dec_eq(x_351, x_352);
if (x_353 == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = l_String_toName(x_351);
x_355 = l_Lean_Name_isAnonymous(x_354);
if (x_355 == 0)
{
lean_dec(x_311);
x_24 = x_354;
goto block_307;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_354);
lean_dec(x_23);
lean_dec(x_22);
x_356 = lean_unsigned_to_nat(80u);
x_357 = l_Lean_Json_pretty(x_311, x_356);
x_358 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_359 = lean_string_append(x_358, x_357);
lean_dec(x_357);
x_360 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_361 = lean_string_append(x_359, x_360);
x_362 = l_Lake_PackageEntry_fromJson_x3f___closed__47;
x_363 = lean_string_append(x_362, x_361);
lean_dec(x_361);
x_364 = l_Lake_Manifest_version___closed__2;
x_365 = lean_string_append(x_363, x_364);
x_366 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_367 = lean_string_append(x_366, x_365);
lean_dec(x_365);
x_368 = lean_string_append(x_367, x_364);
x_369 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_369, 0, x_368);
return x_369;
}
}
else
{
lean_object* x_370; 
lean_dec(x_351);
lean_dec(x_311);
x_370 = lean_box(0);
x_24 = x_370;
goto block_307;
}
}
}
}
block_307:
{
lean_object* x_25; lean_object* x_38; lean_object* x_47; lean_object* x_54; lean_object* x_61; lean_object* x_288; lean_object* x_292; lean_object* x_293; 
x_292 = l_Lake_PackageEntry_toJson___closed__1;
x_293 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_box(0);
x_288 = x_294;
goto block_291;
}
else
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_293);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_293, 0);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
lean_free_object(x_293);
x_297 = lean_box(0);
x_288 = x_297;
goto block_291;
}
else
{
lean_object* x_298; 
x_298 = l_Lean_Json_getStr_x3f(x_296);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; 
lean_free_object(x_293);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
lean_dec(x_298);
x_2 = x_299;
goto block_8;
}
else
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
lean_dec(x_298);
lean_ctor_set(x_293, 0, x_300);
x_288 = x_293;
goto block_291;
}
}
}
else
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_293, 0);
lean_inc(x_301);
lean_dec(x_293);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
x_302 = lean_box(0);
x_288 = x_302;
goto block_291;
}
else
{
lean_object* x_303; 
x_303 = l_Lean_Json_getStr_x3f(x_301);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec(x_303);
x_2 = x_304;
goto block_8;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_288 = x_306;
goto block_291;
}
}
}
}
block_37:
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = 1;
x_27 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_28 = l_Lean_Name_toString(x_24, x_26, x_27);
x_29 = l_Lake_PackageEntry_fromJson_x3f___closed__5;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lake_PackageEntry_fromJson_x3f___closed__6;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_25);
lean_dec(x_25);
x_34 = l_Lake_Manifest_version___closed__2;
x_35 = lean_string_append(x_33, x_34);
if (lean_is_scalar(x_23)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_23;
 lean_ctor_set_tag(x_36, 0);
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
block_46:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_25 = x_39;
goto block_37;
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_23);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = l_Lake_PackageEntry_fromJson_x3f___closed__8;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lake_Manifest_version___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_38 = x_52;
goto block_46;
}
block_60:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l_Lake_PackageEntry_fromJson_x3f___closed__10;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lake_Manifest_version___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_38 = x_59;
goto block_46;
}
block_287:
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lake_PackageEntry_toJson___closed__5;
x_63 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_22);
x_64 = l_Lake_PackageEntry_fromJson_x3f___closed__13;
x_25 = x_64;
goto block_37;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l_Lean_Json_getStr_x3f(x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lake_PackageEntry_fromJson_x3f___closed__15;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lake_Manifest_version___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_25 = x_72;
goto block_37;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
x_75 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_76 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_77 = l_Lake_PackageEntry_fromJson_x3f___closed__18;
x_38 = x_77;
goto block_46;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = l_Lean_Json_getBool_x3f(x_78);
lean_dec(x_78);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lake_PackageEntry_fromJson_x3f___closed__20;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = l_Lake_Manifest_version___closed__2;
x_86 = lean_string_append(x_84, x_85);
lean_ctor_set(x_80, 0, x_86);
x_38 = x_80;
goto block_46;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
lean_dec(x_80);
x_88 = l_Lake_PackageEntry_fromJson_x3f___closed__20;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = l_Lake_Manifest_version___closed__2;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_38 = x_92;
goto block_46;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_268; lean_object* x_272; lean_object* x_273; 
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_94 = x_80;
} else {
 lean_dec_ref(x_80);
 x_94 = lean_box(0);
}
x_272 = l_Lake_PackageEntry_toJson___closed__2;
x_273 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_272);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_box(0);
x_268 = x_274;
goto block_271;
}
else
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_273, 0);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
lean_free_object(x_273);
x_277 = lean_box(0);
x_268 = x_277;
goto block_271;
}
else
{
lean_object* x_278; 
x_278 = l_Lean_Json_getStr_x3f(x_276);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; 
lean_free_object(x_273);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec(x_278);
x_54 = x_279;
goto block_60;
}
else
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
lean_dec(x_278);
lean_ctor_set(x_273, 0, x_280);
x_268 = x_273;
goto block_271;
}
}
}
else
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_273, 0);
lean_inc(x_281);
lean_dec(x_273);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
x_282 = lean_box(0);
x_268 = x_282;
goto block_271;
}
else
{
lean_object* x_283; 
x_283 = l_Lean_Json_getStr_x3f(x_281);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec(x_283);
x_54 = x_284;
goto block_60;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_268 = x_286;
goto block_271;
}
}
}
}
block_267:
{
lean_object* x_96; lean_object* x_248; lean_object* x_252; lean_object* x_253; 
x_252 = l_Lake_PackageEntry_toJson___closed__3;
x_253 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
x_254 = lean_box(0);
x_248 = x_254;
goto block_251;
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_253, 0);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
lean_free_object(x_253);
x_257 = lean_box(0);
x_248 = x_257;
goto block_251;
}
else
{
lean_object* x_258; 
x_258 = l_Lean_Json_getStr_x3f(x_256);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
lean_free_object(x_253);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec(x_258);
x_47 = x_259;
goto block_53;
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec(x_258);
lean_ctor_set(x_253, 0, x_260);
x_248 = x_253;
goto block_251;
}
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_253, 0);
lean_inc(x_261);
lean_dec(x_253);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_box(0);
x_248 = x_262;
goto block_251;
}
else
{
lean_object* x_263; 
x_263 = l_Lean_Json_getStr_x3f(x_261);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec(x_263);
x_47 = x_264;
goto block_53;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_248 = x_266;
goto block_251;
}
}
}
}
block_247:
{
lean_object* x_97; lean_object* x_105; lean_object* x_111; lean_object* x_118; lean_object* x_125; uint8_t x_126; 
x_125 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_126 = lean_string_dec_eq(x_73, x_125);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9;
x_128 = lean_string_dec_eq(x_73, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_129 = l_Lake_PackageEntry_fromJson_x3f___closed__25;
x_130 = lean_string_append(x_129, x_73);
lean_dec(x_73);
x_131 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_132 = lean_string_append(x_130, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_38 = x_133;
goto block_46;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_73);
x_134 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1;
x_135 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_136 = l_Lake_PackageEntry_fromJson_x3f___closed__28;
x_38 = x_136;
goto block_46;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Json_getStr_x3f(x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = l_Lake_PackageEntry_fromJson_x3f___closed__30;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = l_Lake_Manifest_version___closed__2;
x_144 = lean_string_append(x_142, x_143);
lean_ctor_set(x_138, 0, x_144);
x_38 = x_138;
goto block_46;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_138, 0);
lean_inc(x_145);
lean_dec(x_138);
x_146 = l_Lake_PackageEntry_fromJson_x3f___closed__30;
x_147 = lean_string_append(x_146, x_145);
lean_dec(x_145);
x_148 = l_Lake_Manifest_version___closed__2;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_38 = x_150;
goto block_46;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_138, 0);
lean_inc(x_151);
lean_dec(x_138);
x_152 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3;
x_153 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_22);
x_154 = l_Lake_PackageEntry_fromJson_x3f___closed__33;
x_38 = x_154;
goto block_46;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Json_getStr_x3f(x_155);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
lean_dec(x_151);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_22);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = l_Lake_PackageEntry_fromJson_x3f___closed__35;
x_160 = lean_string_append(x_159, x_158);
lean_dec(x_158);
x_161 = l_Lake_Manifest_version___closed__2;
x_162 = lean_string_append(x_160, x_161);
lean_ctor_set(x_156, 0, x_162);
x_105 = x_156;
goto block_110;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_156, 0);
lean_inc(x_163);
lean_dec(x_156);
x_164 = l_Lake_PackageEntry_fromJson_x3f___closed__35;
x_165 = lean_string_append(x_164, x_163);
lean_dec(x_163);
x_166 = l_Lake_Manifest_version___closed__2;
x_167 = lean_string_append(x_165, x_166);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_105 = x_168;
goto block_110;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_202; lean_object* x_203; 
x_169 = lean_ctor_get(x_156, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_170 = x_156;
} else {
 lean_dec_ref(x_156);
 x_170 = lean_box(0);
}
x_202 = l_Lake_PackageEntry_toJson___closed__9;
x_203 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
lean_dec(x_66);
x_204 = lean_box(0);
x_171 = x_204;
goto block_201;
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_203);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_203, 0);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
lean_free_object(x_203);
lean_dec(x_66);
x_207 = lean_box(0);
x_171 = x_207;
goto block_201;
}
else
{
lean_object* x_208; 
x_208 = l_Lean_Json_getStr_x3f(x_206);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
lean_free_object(x_203);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_151);
lean_dec(x_74);
lean_dec(x_22);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec(x_208);
x_118 = x_209;
goto block_124;
}
else
{
lean_object* x_210; 
lean_dec(x_66);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_dec(x_208);
lean_ctor_set(x_203, 0, x_210);
x_171 = x_203;
goto block_201;
}
}
}
else
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_203, 0);
lean_inc(x_211);
lean_dec(x_203);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
lean_dec(x_66);
x_212 = lean_box(0);
x_171 = x_212;
goto block_201;
}
else
{
lean_object* x_213; 
x_213 = l_Lean_Json_getStr_x3f(x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_151);
lean_dec(x_74);
lean_dec(x_22);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec(x_213);
x_118 = x_214;
goto block_124;
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_66);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_171 = x_216;
goto block_201;
}
}
}
}
block_201:
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Lake_PackageEntry_toJson___closed__11;
x_173 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_172);
lean_dec(x_22);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_74);
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_175, 0, x_151);
lean_ctor_set(x_175, 1, x_169);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_174);
if (lean_is_scalar(x_170)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_170;
}
lean_ctor_set(x_176, 0, x_175);
x_105 = x_176;
goto block_110;
}
else
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_173);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_173, 0);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_free_object(x_173);
lean_dec(x_74);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_180, 0, x_151);
lean_ctor_set(x_180, 1, x_169);
lean_ctor_set(x_180, 2, x_171);
lean_ctor_set(x_180, 3, x_179);
if (lean_is_scalar(x_170)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_170;
}
lean_ctor_set(x_181, 0, x_180);
x_105 = x_181;
goto block_110;
}
else
{
lean_object* x_182; 
lean_dec(x_170);
x_182 = l_Lean_Json_getStr_x3f(x_178);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
lean_free_object(x_173);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_151);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_111 = x_183;
goto block_117;
}
else
{
uint8_t x_184; 
lean_dec(x_74);
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_182, 0);
lean_ctor_set(x_173, 0, x_185);
x_186 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_186, 0, x_151);
lean_ctor_set(x_186, 1, x_169);
lean_ctor_set(x_186, 2, x_171);
lean_ctor_set(x_186, 3, x_173);
lean_ctor_set(x_182, 0, x_186);
x_105 = x_182;
goto block_110;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_182, 0);
lean_inc(x_187);
lean_dec(x_182);
lean_ctor_set(x_173, 0, x_187);
x_188 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_188, 0, x_151);
lean_ctor_set(x_188, 1, x_169);
lean_ctor_set(x_188, 2, x_171);
lean_ctor_set(x_188, 3, x_173);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_105 = x_189;
goto block_110;
}
}
}
}
else
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_173, 0);
lean_inc(x_190);
lean_dec(x_173);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_74);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_192, 0, x_151);
lean_ctor_set(x_192, 1, x_169);
lean_ctor_set(x_192, 2, x_171);
lean_ctor_set(x_192, 3, x_191);
if (lean_is_scalar(x_170)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_170;
}
lean_ctor_set(x_193, 0, x_192);
x_105 = x_193;
goto block_110;
}
else
{
lean_object* x_194; 
lean_dec(x_170);
x_194 = l_Lean_Json_getStr_x3f(x_190);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_151);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_111 = x_195;
goto block_117;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_74);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_196);
x_199 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_199, 0, x_151);
lean_ctor_set(x_199, 1, x_169);
lean_ctor_set(x_199, 2, x_171);
lean_ctor_set(x_199, 3, x_198);
if (lean_is_scalar(x_197)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_197;
}
lean_ctor_set(x_200, 0, x_199);
x_105 = x_200;
goto block_110;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
x_217 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_218 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_22, x_217);
lean_dec(x_22);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_61);
x_219 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_38 = x_219;
goto block_46;
}
else
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_218, 0);
x_222 = l_Lean_Json_getStr_x3f(x_221);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
lean_free_object(x_218);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_61);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = l_Lake_PackageEntry_fromJson_x3f___closed__40;
x_226 = lean_string_append(x_225, x_224);
lean_dec(x_224);
x_227 = l_Lake_Manifest_version___closed__2;
x_228 = lean_string_append(x_226, x_227);
lean_ctor_set(x_222, 0, x_228);
x_38 = x_222;
goto block_46;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_ctor_get(x_222, 0);
lean_inc(x_229);
lean_dec(x_222);
x_230 = l_Lake_PackageEntry_fromJson_x3f___closed__40;
x_231 = lean_string_append(x_230, x_229);
lean_dec(x_229);
x_232 = l_Lake_Manifest_version___closed__2;
x_233 = lean_string_append(x_231, x_232);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_38 = x_234;
goto block_46;
}
}
else
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_222, 0);
lean_inc(x_235);
lean_dec(x_222);
lean_ctor_set_tag(x_218, 0);
lean_ctor_set(x_218, 0, x_235);
x_97 = x_218;
goto block_104;
}
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_218, 0);
lean_inc(x_236);
lean_dec(x_218);
x_237 = l_Lean_Json_getStr_x3f(x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_61);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = l_Lake_PackageEntry_fromJson_x3f___closed__40;
x_241 = lean_string_append(x_240, x_238);
lean_dec(x_238);
x_242 = l_Lake_Manifest_version___closed__2;
x_243 = lean_string_append(x_241, x_242);
if (lean_is_scalar(x_239)) {
 x_244 = lean_alloc_ctor(0, 1, 0);
} else {
 x_244 = x_239;
}
lean_ctor_set(x_244, 0, x_243);
x_38 = x_244;
goto block_46;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_237, 0);
lean_inc(x_245);
lean_dec(x_237);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_97 = x_246;
goto block_104;
}
}
}
}
block_104:
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
if (lean_is_scalar(x_79)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_79;
}
lean_ctor_set(x_98, 0, x_96);
lean_inc(x_24);
x_99 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_99, 0, x_24);
lean_ctor_set(x_99, 1, x_61);
lean_ctor_set(x_99, 2, x_95);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set(x_99, 4, x_97);
x_100 = lean_unbox(x_93);
lean_dec(x_93);
lean_ctor_set_uint8(x_99, sizeof(void*)*5, x_100);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
if (lean_is_scalar(x_94)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_94;
}
lean_ctor_set(x_103, 0, x_102);
x_38 = x_103;
goto block_46;
}
block_110:
{
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_61);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
x_38 = x_105;
goto block_46;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_38 = x_108;
goto block_46;
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
lean_dec(x_105);
x_97 = x_109;
goto block_104;
}
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = l_Lake_PackageEntry_fromJson_x3f___closed__22;
x_113 = lean_string_append(x_112, x_111);
lean_dec(x_111);
x_114 = l_Lake_Manifest_version___closed__2;
x_115 = lean_string_append(x_113, x_114);
if (lean_is_scalar(x_74)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_74;
 lean_ctor_set_tag(x_116, 0);
}
lean_ctor_set(x_116, 0, x_115);
x_105 = x_116;
goto block_110;
}
block_124:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = l_Lake_PackageEntry_fromJson_x3f___closed__24;
x_120 = lean_string_append(x_119, x_118);
lean_dec(x_118);
x_121 = l_Lake_Manifest_version___closed__2;
x_122 = lean_string_append(x_120, x_121);
if (lean_is_scalar(x_66)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_66;
 lean_ctor_set_tag(x_123, 0);
}
lean_ctor_set(x_123, 0, x_122);
x_105 = x_123;
goto block_110;
}
}
block_251:
{
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = l_Lake_defaultManifestFile;
x_96 = x_249;
goto block_247;
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_dec(x_248);
x_96 = x_250;
goto block_247;
}
}
}
block_271:
{
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; 
x_269 = l_Lake_defaultConfigFile;
x_95 = x_269;
goto block_267;
}
else
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
lean_dec(x_268);
x_95 = x_270;
goto block_267;
}
}
}
}
}
}
}
block_291:
{
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
x_289 = l_Lake_Manifest_version___closed__2;
x_61 = x_289;
goto block_287;
}
else
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
x_61 = x_290;
goto block_287;
}
}
}
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_PackageEntry_fromJson_x3f___closed__3;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = l_Lake_Manifest_version___closed__2;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lake_PackageEntry_instFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_PackageEntry_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageEntry_instFromJson___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*5, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 2);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
lean_dec(x_4);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_1);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 4);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = l_System_FilePath_join(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_System_FilePath_join(x_1, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_2, 4, x_11);
return x_2;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_18 = x_3;
} else {
 lean_dec_ref(x_3);
 x_18 = lean_box(0);
}
x_19 = l_System_FilePath_join(x_1, x_17);
lean_dec(x_17);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 4);
lean_dec(x_23);
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_3);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_26);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_Lake_Manifest_version___closed__2;
x_8 = l_Lake_defaultConfigFile;
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
x_18 = l_Lake_Manifest_version___closed__2;
x_19 = l_Lake_defaultConfigFile;
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_11);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageEntry_ofV6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 3, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_PackageEntry_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_version___closed__3;
x_2 = l_Lake_StdVer_toString(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_toJson___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("version", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_toJson___closed__3;
x_2 = l_Lake_Manifest_toJson___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakeDir", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packages", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packagesDir", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_toJson___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lake_mkRelPathString(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lake_Manifest_toJson___closed__5;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1(x_16, x_17, x_15);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lake_Manifest_toJson___closed__6;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = l_Lake_Manifest_toJson___closed__8;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lake_Manifest_toJson___closed__4;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Json_mkObj(x_29);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = l_Lake_mkRelPathString(x_32);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 0, x_33);
x_34 = l_Lake_Manifest_toJson___closed__7;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lake_Manifest_toJson___closed__4;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Json_mkObj(x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
lean_dec(x_14);
x_43 = l_Lake_mkRelPathString(x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lake_Manifest_toJson___closed__7;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_23);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_13);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lake_Manifest_toJson___closed__4;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Json_mkObj(x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Manifest_instToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Manifest_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Manifest_instToJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getVersion___lambda__1___closed__1;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("incompatible manifest version '", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("schema version '", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is of a higher major version than this Lake's '", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'; you may need to update your 'lean-toolchain'", 47, 47);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lake_instOrdStdVer;
x_7 = l_Lake_Manifest_getVersion___lambda__1___closed__2;
lean_inc(x_1);
x_8 = l_Ord_instDecidableRelLt___rarg(x_6, x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_10 = l_Lake_StdVer_toString(x_1);
x_11 = l_Lake_Manifest_getVersion___lambda__1___closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_16 = l_Lake_StdVer_toString(x_1);
x_17 = l_Lake_Manifest_getVersion___lambda__1___closed__4;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_Manifest_getVersion___lambda__1___closed__5;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lake_Manifest_toJson___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Manifest_getVersion___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid version '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("schemaVersion", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l_Lake_Manifest_getVersion___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getVersion___closed__5;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_getVersion___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_110; lean_object* x_111; 
x_110 = l_Lake_Manifest_toJson___closed__3;
x_111 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Lake_Manifest_getVersion___closed__4;
x_113 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = l_Lake_Manifest_getVersion___closed__7;
return x_114;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_2 = x_115;
goto block_109;
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
lean_dec(x_111);
x_2 = x_116;
goto block_109;
}
block_109:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_getVersion___closed__1;
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lake_Manifest_getVersion___closed__3;
x_9 = lean_int_dec_lt(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_nat_abs(x_6);
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
lean_dec(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
lean_free_object(x_4);
x_13 = lean_unsigned_to_nat(80u);
lean_inc(x_2);
x_14 = l_Lean_Json_pretty(x_2, x_13);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = l_Lake_Manifest_getVersion___closed__2;
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_20 = lean_string_append(x_18, x_19);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_21 = l_Lake_Manifest_getVersion___closed__2;
x_22 = lean_string_append(x_21, x_14);
lean_dec(x_14);
x_23 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_26, 2, x_11);
x_27 = l_Lake_Manifest_version___closed__2;
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_26);
x_28 = lean_apply_1(x_3, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_7);
lean_dec(x_6);
x_29 = lean_unsigned_to_nat(80u);
lean_inc(x_2);
x_30 = l_Lean_Json_pretty(x_2, x_29);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_2, 0);
lean_dec(x_32);
x_33 = l_Lake_Manifest_getVersion___closed__2;
x_34 = lean_string_append(x_33, x_30);
lean_dec(x_30);
x_35 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_36 = lean_string_append(x_34, x_35);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_36);
return x_2;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_37 = l_Lake_Manifest_getVersion___closed__2;
x_38 = lean_string_append(x_37, x_30);
lean_dec(x_30);
x_39 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = l_Lake_Manifest_getVersion___closed__3;
x_45 = lean_int_dec_lt(x_42, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_nat_abs(x_42);
lean_dec(x_42);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_43, x_47);
lean_dec(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(80u);
lean_inc(x_2);
x_50 = l_Lean_Json_pretty(x_2, x_49);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_51 = x_2;
} else {
 lean_dec_ref(x_2);
 x_51 = lean_box(0);
}
x_52 = l_Lake_Manifest_getVersion___closed__2;
x_53 = lean_string_append(x_52, x_50);
lean_dec(x_50);
x_54 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_55 = lean_string_append(x_53, x_54);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_51;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_47);
x_58 = l_Lake_Manifest_version___closed__2;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_apply_1(x_3, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_42);
x_61 = lean_unsigned_to_nat(80u);
lean_inc(x_2);
x_62 = l_Lean_Json_pretty(x_2, x_61);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_63 = x_2;
} else {
 lean_dec_ref(x_2);
 x_63 = lean_box(0);
}
x_64 = l_Lake_Manifest_getVersion___closed__2;
x_65 = lean_string_append(x_64, x_62);
lean_dec(x_62);
x_66 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_67 = lean_string_append(x_65, x_66);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_63;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
case 3:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
lean_dec(x_2);
x_70 = l_Lake_StdVer_parse(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_apply_1(x_3, x_74);
return x_75;
}
}
case 4:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_unsigned_to_nat(80u);
lean_inc(x_2);
x_77 = l_Lean_Json_pretty(x_2, x_76);
x_78 = !lean_is_exclusive(x_2);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_2, 0);
lean_dec(x_79);
x_80 = l_Lake_Manifest_getVersion___closed__2;
x_81 = lean_string_append(x_80, x_77);
lean_dec(x_77);
x_82 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_83 = lean_string_append(x_81, x_82);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_83);
return x_2;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_84 = l_Lake_Manifest_getVersion___closed__2;
x_85 = lean_string_append(x_84, x_77);
lean_dec(x_77);
x_86 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
case 5:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_unsigned_to_nat(80u);
lean_inc(x_2);
x_90 = l_Lean_Json_pretty(x_2, x_89);
x_91 = !lean_is_exclusive(x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_2, 0);
lean_dec(x_92);
x_93 = l_Lake_Manifest_getVersion___closed__2;
x_94 = lean_string_append(x_93, x_90);
lean_dec(x_90);
x_95 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_96 = lean_string_append(x_94, x_95);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_96);
return x_2;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_2);
x_97 = l_Lake_Manifest_getVersion___closed__2;
x_98 = lean_string_append(x_97, x_90);
lean_dec(x_90);
x_99 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
default: 
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_unsigned_to_nat(80u);
x_103 = l_Lean_Json_pretty(x_2, x_102);
x_104 = l_Lake_Manifest_getVersion___closed__2;
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
x_106 = l_Lake_Manifest_getVersion___lambda__1___closed__6;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Manifest_getVersion(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_PackageEntry_ofV6(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lake_PackageEntry_fromJson_x3f(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getPackages___closed__1;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lake_Manifest_getPackages___closed__4() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_Manifest_getPackages___closed__3;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getPackages___closed__5;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_getPackages___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lake_instOrdStdVer;
x_28 = l_Lake_Manifest_getPackages___closed__6;
x_29 = l_Ord_instDecidableRelLt___rarg(x_27, x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lake_Manifest_toJson___closed__6;
x_31 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l_Lake_Manifest_getPackages___closed__7;
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; 
x_34 = l_Lake_Manifest_getPackages___closed__7;
return x_34;
}
case 4:
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_size(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__2(x_36, x_37, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_3 = x_39;
goto block_9;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
default: 
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_unsigned_to_nat(80u);
x_44 = l_Lean_Json_pretty(x_33, x_43);
x_45 = l_Lake_Manifest_getPackages___closed__8;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_48 = lean_string_append(x_46, x_47);
x_3 = x_48;
goto block_9;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lake_Manifest_toJson___closed__6;
x_50 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_10 = x_51;
goto block_26;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
switch (lean_obj_tag(x_53)) {
case 0:
{
lean_object* x_54; 
lean_free_object(x_50);
x_54 = lean_box(0);
x_10 = x_54;
goto block_26;
}
case 4:
{
lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_size(x_55);
x_57 = 0;
x_58 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3(x_56, x_57, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_free_object(x_50);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_3 = x_59;
goto block_9;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
lean_ctor_set(x_50, 0, x_60);
x_10 = x_50;
goto block_26;
}
}
default: 
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_50);
x_61 = lean_unsigned_to_nat(80u);
x_62 = l_Lean_Json_pretty(x_53, x_61);
x_63 = l_Lake_Manifest_getPackages___closed__8;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_66 = lean_string_append(x_64, x_65);
x_3 = x_66;
goto block_9;
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_50, 0);
lean_inc(x_67);
lean_dec(x_50);
switch (lean_obj_tag(x_67)) {
case 0:
{
lean_object* x_68; 
x_68 = lean_box(0);
x_10 = x_68;
goto block_26;
}
case 4:
{
lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_array_size(x_69);
x_71 = 0;
x_72 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3(x_70, x_71, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_3 = x_73;
goto block_9;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_10 = x_75;
goto block_26;
}
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_unsigned_to_nat(80u);
x_77 = l_Lean_Json_pretty(x_67, x_76);
x_78 = l_Lake_Manifest_getPackages___closed__8;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_81 = lean_string_append(x_79, x_80);
x_3 = x_81;
goto block_9;
}
}
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_Manifest_getPackages___closed__2;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lake_Manifest_version___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_26:
{
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = 0;
x_12 = l_Lake_Manifest_getPackages___closed__4;
x_13 = l_Lake_Manifest_getPackages___closed__3;
x_14 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_12, x_11, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_18, x_19, x_17);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_array_size(x_21);
x_23 = 0;
x_24 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_22, x_23, x_21);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_getPackages(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___closed__1;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___closed__3;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_9; lean_object* x_16; lean_object* x_23; 
x_23 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lake_Manifest_getVersion(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_85; lean_object* x_89; lean_object* x_90; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_89 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_90 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_27, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
x_85 = x_91;
goto block_88;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_90, 0);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_free_object(x_90);
x_94 = lean_box(0);
x_85 = x_94;
goto block_88;
}
else
{
lean_object* x_95; 
lean_inc(x_93);
x_95 = l_Lean_Json_getStr_x3f(x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_free_object(x_90);
lean_dec(x_93);
lean_dec(x_32);
lean_dec(x_27);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
x_16 = x_96;
goto block_22;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_99 = lean_string_dec_eq(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_String_toName(x_97);
x_101 = l_Lean_Name_isAnonymous(x_100);
if (x_101 == 0)
{
lean_dec(x_93);
lean_ctor_set(x_90, 0, x_100);
x_85 = x_90;
goto block_88;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_100);
lean_free_object(x_90);
lean_dec(x_32);
lean_dec(x_27);
x_102 = lean_unsigned_to_nat(80u);
x_103 = l_Lean_Json_pretty(x_93, x_102);
x_104 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
x_106 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_107 = lean_string_append(x_105, x_106);
x_16 = x_107;
goto block_22;
}
}
else
{
lean_object* x_108; 
lean_dec(x_97);
lean_free_object(x_90);
lean_dec(x_93);
x_108 = l_Lake_Manifest_fromJson_x3f___closed__5;
x_85 = x_108;
goto block_88;
}
}
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
lean_dec(x_90);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_box(0);
x_85 = x_110;
goto block_88;
}
else
{
lean_object* x_111; 
lean_inc(x_109);
x_111 = l_Lean_Json_getStr_x3f(x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_32);
lean_dec(x_27);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_16 = x_112;
goto block_22;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11;
x_115 = lean_string_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_String_toName(x_113);
x_117 = l_Lean_Name_isAnonymous(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_109);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_85 = x_118;
goto block_88;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_32);
lean_dec(x_27);
x_119 = lean_unsigned_to_nat(80u);
x_120 = l_Lean_Json_pretty(x_109, x_119);
x_121 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13;
x_124 = lean_string_append(x_122, x_123);
x_16 = x_124;
goto block_22;
}
}
else
{
lean_object* x_125; 
lean_dec(x_113);
lean_dec(x_109);
x_125 = l_Lake_Manifest_fromJson_x3f___closed__5;
x_85 = x_125;
goto block_88;
}
}
}
}
}
block_84:
{
lean_object* x_34; lean_object* x_65; lean_object* x_69; lean_object* x_70; 
x_69 = l_Lake_Manifest_toJson___closed__5;
x_70 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_27, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_65 = x_71;
goto block_68;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 0);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_free_object(x_70);
x_74 = lean_box(0);
x_65 = x_74;
goto block_68;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_Json_getStr_x3f(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_free_object(x_70);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_9 = x_76;
goto block_15;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
lean_ctor_set(x_70, 0, x_77);
x_65 = x_70;
goto block_68;
}
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_65 = x_79;
goto block_68;
}
else
{
lean_object* x_80; 
x_80 = l_Lean_Json_getStr_x3f(x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_9 = x_81;
goto block_15;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_65 = x_83;
goto block_68;
}
}
}
}
block_64:
{
lean_object* x_35; lean_object* x_49; lean_object* x_50; 
x_49 = l_Lake_Manifest_toJson___closed__7;
x_50 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_27, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_35 = x_51;
goto block_48;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_free_object(x_50);
x_54 = lean_box(0);
x_35 = x_54;
goto block_48;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_Json_getStr_x3f(x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_free_object(x_50);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_2 = x_56;
goto block_8;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_50, 0, x_57);
x_35 = x_50;
goto block_48;
}
}
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_35 = x_59;
goto block_48;
}
else
{
lean_object* x_60; 
x_60 = l_Lean_Json_getStr_x3f(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_2 = x_61;
goto block_8;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_35 = x_63;
goto block_48;
}
}
}
}
block_48:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lake_Manifest_version___closed__2;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lake_Manifest_getPackages(x_37, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_38, 0, x_44);
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
block_68:
{
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = l_Lake_defaultLakeDir;
x_34 = x_66;
goto block_64;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_34 = x_67;
goto block_64;
}
}
}
block_88:
{
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_box(0);
x_33 = x_86;
goto block_84;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_33 = x_87;
goto block_84;
}
}
}
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Manifest_fromJson_x3f___closed__2;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = l_Lake_Manifest_version___closed__2;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_Manifest_version___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lake_PackageEntry_fromJson_x3f___closed__47;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_Manifest_version___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
static lean_object* _init_l_Lake_Manifest_instFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Manifest_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Manifest_instFromJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_parse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Manifest_parse___closed__1;
x_3 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_Manifest_parse___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lake_Manifest_version___closed__2;
x_9 = lean_string_append(x_7, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lake_Manifest_parse___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Manifest_version___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Lake_Manifest_fromJson_x3f(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_Manifest_parse___closed__1;
x_7 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lake_Manifest_parse___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_Manifest_version___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_12, x_1);
x_15 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = lean_string_append(x_17, x_12);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lake_Manifest_parse___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lake_Manifest_version___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_22, x_1);
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_23);
lean_dec(x_23);
x_28 = lean_string_append(x_27, x_22);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = l_Lake_Manifest_fromJson_x3f(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lake_Manifest_version___closed__2;
x_35 = lean_string_append(x_34, x_1);
x_36 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_33);
lean_dec(x_33);
x_39 = lean_string_append(x_38, x_34);
lean_ctor_set_tag(x_31, 18);
lean_ctor_set(x_31, 0, x_39);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lake_Manifest_version___closed__2;
x_42 = lean_string_append(x_41, x_1);
x_43 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_40);
lean_dec(x_40);
x_46 = lean_string_append(x_45, x_41);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_47);
return x_3;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
lean_ctor_set(x_3, 0, x_48);
return x_3;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = l_Lake_Manifest_parse___closed__1;
x_52 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_51, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = l_Lake_Manifest_parse___closed__2;
x_56 = lean_string_append(x_55, x_53);
lean_dec(x_53);
x_57 = l_Lake_Manifest_version___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_57, x_1);
x_60 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_58);
lean_dec(x_58);
x_63 = lean_string_append(x_62, x_57);
if (lean_is_scalar(x_54)) {
 x_64 = lean_alloc_ctor(18, 1, 0);
} else {
 x_64 = x_54;
 lean_ctor_set_tag(x_64, 18);
}
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
lean_dec(x_52);
x_67 = l_Lake_Manifest_fromJson_x3f(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Lake_Manifest_version___closed__2;
x_71 = lean_string_append(x_70, x_1);
x_72 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_string_append(x_73, x_68);
lean_dec(x_68);
x_75 = lean_string_append(x_74, x_70);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(18, 1, 0);
} else {
 x_76 = x_69;
 lean_ctor_set_tag(x_76, 18);
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_50);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_50);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_3);
if (x_80 == 0)
{
return x_3;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_3);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_load(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_15; 
x_15 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lake_Manifest_parse___closed__1;
x_19 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lake_Manifest_parse___closed__2;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_Manifest_version___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_24, x_1);
x_27 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
x_30 = lean_string_append(x_29, x_24);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_19, 0, x_31);
x_3 = x_19;
x_4 = x_17;
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = l_Lake_Manifest_parse___closed__2;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lake_Manifest_version___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_35, x_1);
x_38 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_36);
lean_dec(x_36);
x_41 = lean_string_append(x_40, x_35);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_3 = x_43;
x_4 = x_17;
goto block_14;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
lean_dec(x_19);
x_45 = l_Lake_Manifest_fromJson_x3f(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lake_Manifest_version___closed__2;
x_49 = lean_string_append(x_48, x_1);
x_50 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_47);
lean_dec(x_47);
x_53 = lean_string_append(x_52, x_48);
x_54 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_45, 0, x_54);
x_3 = x_45;
x_4 = x_17;
goto block_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = l_Lake_Manifest_version___closed__2;
x_57 = lean_string_append(x_56, x_1);
x_58 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_55);
lean_dec(x_55);
x_61 = lean_string_append(x_60, x_56);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_3 = x_63;
x_4 = x_17;
goto block_14;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
x_3 = x_45;
x_4 = x_17;
goto block_14;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_45, 0);
lean_inc(x_65);
lean_dec(x_45);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_3 = x_66;
x_4 = x_17;
goto block_14;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_15, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_15, 1);
lean_inc(x_68);
lean_dec(x_15);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_3 = x_69;
x_4 = x_68;
goto block_14;
}
block_14:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 11)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_load_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lake_Manifest_toJson(x_1);
x_5 = lean_unsigned_to_nat(80u);
x_6 = l_Lean_Json_pretty(x_4, x_5);
x_7 = 10;
x_8 = lean_string_push(x_6, x_7);
x_9 = l_IO_FS_writeFile(x_2, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_save(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_save(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_saveToFile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lake_Manifest_getVersion(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lake_Manifest_version___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_Manifest_getPackages(x_13, x_6);
lean_dec(x_6);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Manifest_parse___closed__1;
x_3 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_Manifest_parse___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lake_Manifest_version___closed__2;
x_9 = lean_string_append(x_7, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lake_Manifest_parse___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Manifest_version___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Lake_Manifest_decodeEntries(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_Manifest_parse___closed__1;
x_7 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lake_Manifest_parse___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_Manifest_version___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_12, x_1);
x_15 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = lean_string_append(x_17, x_12);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lake_Manifest_parse___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lake_Manifest_version___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_22, x_1);
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_23);
lean_dec(x_23);
x_28 = lean_string_append(x_27, x_22);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = l_Lake_Manifest_decodeEntries(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lake_Manifest_version___closed__2;
x_35 = lean_string_append(x_34, x_1);
x_36 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_33);
lean_dec(x_33);
x_39 = lean_string_append(x_38, x_34);
lean_ctor_set_tag(x_31, 18);
lean_ctor_set(x_31, 0, x_39);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lake_Manifest_version___closed__2;
x_42 = lean_string_append(x_41, x_1);
x_43 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_40);
lean_dec(x_40);
x_46 = lean_string_append(x_45, x_41);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_47);
return x_3;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
lean_ctor_set(x_3, 0, x_48);
return x_3;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = l_Lake_Manifest_parse___closed__1;
x_52 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_51, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = l_Lake_Manifest_parse___closed__2;
x_56 = lean_string_append(x_55, x_53);
lean_dec(x_53);
x_57 = l_Lake_Manifest_version___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_57, x_1);
x_60 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_58);
lean_dec(x_58);
x_63 = lean_string_append(x_62, x_57);
if (lean_is_scalar(x_54)) {
 x_64 = lean_alloc_ctor(18, 1, 0);
} else {
 x_64 = x_54;
 lean_ctor_set_tag(x_64, 18);
}
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
lean_dec(x_52);
x_67 = l_Lake_Manifest_decodeEntries(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Lake_Manifest_version___closed__2;
x_71 = lean_string_append(x_70, x_1);
x_72 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_string_append(x_73, x_68);
lean_dec(x_68);
x_75 = lean_string_append(x_74, x_70);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(18, 1, 0);
} else {
 x_76 = x_69;
 lean_ctor_set_tag(x_76, 18);
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_50);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_50);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_3);
if (x_80 == 0)
{
return x_3;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_3);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_loadEntries(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_56; 
x_56 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lake_Manifest_parse___closed__1;
x_60 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_59, x_57);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l_Lake_Manifest_parse___closed__2;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Lake_Manifest_version___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_string_append(x_65, x_1);
x_68 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_string_append(x_69, x_66);
lean_dec(x_66);
x_71 = lean_string_append(x_70, x_65);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_60, 0, x_72);
x_3 = x_60;
x_4 = x_58;
goto block_55;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
lean_dec(x_60);
x_74 = l_Lake_Manifest_parse___closed__2;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lake_Manifest_version___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_76, x_1);
x_79 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_string_append(x_80, x_77);
lean_dec(x_77);
x_82 = lean_string_append(x_81, x_76);
x_83 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_3 = x_84;
x_4 = x_58;
goto block_55;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_60, 0);
lean_inc(x_85);
lean_dec(x_60);
x_86 = l_Lake_Manifest_decodeEntries(x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = l_Lake_Manifest_version___closed__2;
x_90 = lean_string_append(x_89, x_1);
x_91 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_88);
lean_dec(x_88);
x_94 = lean_string_append(x_93, x_89);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_86, 0, x_95);
x_3 = x_86;
x_4 = x_58;
goto block_55;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
lean_dec(x_86);
x_97 = l_Lake_Manifest_version___closed__2;
x_98 = lean_string_append(x_97, x_1);
x_99 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_string_append(x_100, x_96);
lean_dec(x_96);
x_102 = lean_string_append(x_101, x_97);
x_103 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_3 = x_104;
x_4 = x_58;
goto block_55;
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_86);
if (x_105 == 0)
{
x_3 = x_86;
x_4 = x_58;
goto block_55;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_86, 0);
lean_inc(x_106);
lean_dec(x_86);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_3 = x_107;
x_4 = x_58;
goto block_55;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_56, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_56, 1);
lean_inc(x_109);
lean_dec(x_56);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
x_3 = x_110;
x_4 = x_109;
goto block_55;
}
block_55:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_6)) {
case 11:
{
lean_object* x_7; lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_7 = l_Lake_Manifest_getPackages___closed__3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
case 18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_3);
x_9 = l_Lake_Manifest_version___closed__2;
x_10 = lean_string_append(x_9, x_1);
x_11 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_12 = lean_string_append(x_10, x_11);
lean_inc(x_6);
x_13 = lean_io_error_to_string(x_6);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_17 = lean_string_append(x_16, x_9);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_19 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_20 = lean_string_append(x_19, x_9);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = l_Lake_Manifest_version___closed__2;
x_24 = lean_string_append(x_23, x_1);
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_io_error_to_string(x_6);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_28, x_23);
lean_ctor_set_tag(x_3, 18);
lean_ctor_set(x_3, 0, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
switch (lean_obj_tag(x_31)) {
case 11:
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_31);
x_32 = l_Lake_Manifest_getPackages___closed__3;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
case 18:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = l_Lake_Manifest_version___closed__2;
x_35 = lean_string_append(x_34, x_1);
x_36 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_37 = lean_string_append(x_35, x_36);
lean_inc(x_31);
x_38 = lean_io_error_to_string(x_31);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
x_40 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_41 = lean_string_append(x_40, x_34);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(18, 1, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
return x_43;
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = l_Lake_Manifest_version___closed__2;
x_45 = lean_string_append(x_44, x_1);
x_46 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_io_error_to_string(x_31);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_44);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_4);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_tryLoadEntries(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getVersion___closed__4;
x_2 = l_Lake_Manifest_toJson___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1(x_4, x_5, x_2);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lake_Manifest_toJson___closed__6;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_Manifest_saveEntries___closed__1;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Json_mkObj(x_13);
x_15 = lean_unsigned_to_nat(80u);
x_16 = l_Lean_Json_pretty(x_14, x_15);
x_17 = 10;
x_18 = lean_string_push(x_16, x_17);
x_19 = l_IO_FS_writeFile(x_1, x_18, x_3);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_saveEntries(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Version(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Manifest(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Manifest_version___closed__1 = _init_l_Lake_Manifest_version___closed__1();
lean_mark_persistent(l_Lake_Manifest_version___closed__1);
l_Lake_Manifest_version___closed__2 = _init_l_Lake_Manifest_version___closed__2();
lean_mark_persistent(l_Lake_Manifest_version___closed__2);
l_Lake_Manifest_version___closed__3 = _init_l_Lake_Manifest_version___closed__3();
lean_mark_persistent(l_Lake_Manifest_version___closed__3);
l_Lake_Manifest_version = _init_l_Lake_Manifest_version();
lean_mark_persistent(l_Lake_Manifest_version);
l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1 = _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1);
l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__2 = _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__3);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__4 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__4();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__4);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__5);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__6 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__6();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__6);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__7);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__8 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__8();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__8);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__9);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__10);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__11);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__12);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__3___closed__13);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__8 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__8();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__8);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15);
l_Lake_instFromJsonPackageEntryV6___closed__1 = _init_l_Lake_instFromJsonPackageEntryV6___closed__1();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6___closed__1);
l_Lake_instFromJsonPackageEntryV6 = _init_l_Lake_instFromJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6);
l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1 = _init_l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1);
l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__1);
l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____closed__2);
l_Lake_instToJsonPackageEntryV6___closed__1 = _init_l_Lake_instToJsonPackageEntryV6___closed__1();
lean_mark_persistent(l_Lake_instToJsonPackageEntryV6___closed__1);
l_Lake_instToJsonPackageEntryV6 = _init_l_Lake_instToJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instToJsonPackageEntryV6);
l_Lake_instInhabitedPackageEntryV6___closed__1 = _init_l_Lake_instInhabitedPackageEntryV6___closed__1();
lean_mark_persistent(l_Lake_instInhabitedPackageEntryV6___closed__1);
l_Lake_instInhabitedPackageEntryV6 = _init_l_Lake_instInhabitedPackageEntryV6();
lean_mark_persistent(l_Lake_instInhabitedPackageEntryV6);
l_Lake_instInhabitedPackageEntrySrc___closed__1 = _init_l_Lake_instInhabitedPackageEntrySrc___closed__1();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc___closed__1);
l_Lake_instInhabitedPackageEntrySrc = _init_l_Lake_instInhabitedPackageEntrySrc();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc);
l_Lake_instInhabitedPackageEntry___closed__1 = _init_l_Lake_instInhabitedPackageEntry___closed__1();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry___closed__1);
l_Lake_instInhabitedPackageEntry = _init_l_Lake_instInhabitedPackageEntry();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry);
l_Lake_PackageEntry_toJson___closed__1 = _init_l_Lake_PackageEntry_toJson___closed__1();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__1);
l_Lake_PackageEntry_toJson___closed__2 = _init_l_Lake_PackageEntry_toJson___closed__2();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__2);
l_Lake_PackageEntry_toJson___closed__3 = _init_l_Lake_PackageEntry_toJson___closed__3();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__3);
l_Lake_PackageEntry_toJson___closed__4 = _init_l_Lake_PackageEntry_toJson___closed__4();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__4);
l_Lake_PackageEntry_toJson___closed__5 = _init_l_Lake_PackageEntry_toJson___closed__5();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__5);
l_Lake_PackageEntry_toJson___closed__6 = _init_l_Lake_PackageEntry_toJson___closed__6();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__6);
l_Lake_PackageEntry_toJson___closed__7 = _init_l_Lake_PackageEntry_toJson___closed__7();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__7);
l_Lake_PackageEntry_toJson___closed__8 = _init_l_Lake_PackageEntry_toJson___closed__8();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__8);
l_Lake_PackageEntry_toJson___closed__9 = _init_l_Lake_PackageEntry_toJson___closed__9();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__9);
l_Lake_PackageEntry_toJson___closed__10 = _init_l_Lake_PackageEntry_toJson___closed__10();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__10);
l_Lake_PackageEntry_toJson___closed__11 = _init_l_Lake_PackageEntry_toJson___closed__11();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__11);
l_Lake_PackageEntry_toJson___closed__12 = _init_l_Lake_PackageEntry_toJson___closed__12();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__12);
l_Lake_PackageEntry_toJson___closed__13 = _init_l_Lake_PackageEntry_toJson___closed__13();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__13);
l_Lake_PackageEntry_toJson___closed__14 = _init_l_Lake_PackageEntry_toJson___closed__14();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__14);
l_Lake_PackageEntry_instToJson___closed__1 = _init_l_Lake_PackageEntry_instToJson___closed__1();
lean_mark_persistent(l_Lake_PackageEntry_instToJson___closed__1);
l_Lake_PackageEntry_instToJson = _init_l_Lake_PackageEntry_instToJson();
lean_mark_persistent(l_Lake_PackageEntry_instToJson);
l_Lake_PackageEntry_fromJson_x3f___closed__1 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__1);
l_Lake_PackageEntry_fromJson_x3f___closed__2 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__2);
l_Lake_PackageEntry_fromJson_x3f___closed__3 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__3);
l_Lake_PackageEntry_fromJson_x3f___closed__4 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__4);
l_Lake_PackageEntry_fromJson_x3f___closed__5 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__5);
l_Lake_PackageEntry_fromJson_x3f___closed__6 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__6();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__6);
l_Lake_PackageEntry_fromJson_x3f___closed__7 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__7();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__7);
l_Lake_PackageEntry_fromJson_x3f___closed__8 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__8();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__8);
l_Lake_PackageEntry_fromJson_x3f___closed__9 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__9();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__9);
l_Lake_PackageEntry_fromJson_x3f___closed__10 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__10();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__10);
l_Lake_PackageEntry_fromJson_x3f___closed__11 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__11();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__11);
l_Lake_PackageEntry_fromJson_x3f___closed__12 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__12();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__12);
l_Lake_PackageEntry_fromJson_x3f___closed__13 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__13();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__13);
l_Lake_PackageEntry_fromJson_x3f___closed__14 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__14();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__14);
l_Lake_PackageEntry_fromJson_x3f___closed__15 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__15();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__15);
l_Lake_PackageEntry_fromJson_x3f___closed__16 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__16();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__16);
l_Lake_PackageEntry_fromJson_x3f___closed__17 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__17();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__17);
l_Lake_PackageEntry_fromJson_x3f___closed__18 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__18();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__18);
l_Lake_PackageEntry_fromJson_x3f___closed__19 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__19();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__19);
l_Lake_PackageEntry_fromJson_x3f___closed__20 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__20();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__20);
l_Lake_PackageEntry_fromJson_x3f___closed__21 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__21();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__21);
l_Lake_PackageEntry_fromJson_x3f___closed__22 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__22();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__22);
l_Lake_PackageEntry_fromJson_x3f___closed__23 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__23();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__23);
l_Lake_PackageEntry_fromJson_x3f___closed__24 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__24();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__24);
l_Lake_PackageEntry_fromJson_x3f___closed__25 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__25();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__25);
l_Lake_PackageEntry_fromJson_x3f___closed__26 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__26();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__26);
l_Lake_PackageEntry_fromJson_x3f___closed__27 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__27();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__27);
l_Lake_PackageEntry_fromJson_x3f___closed__28 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__28();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__28);
l_Lake_PackageEntry_fromJson_x3f___closed__29 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__29();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__29);
l_Lake_PackageEntry_fromJson_x3f___closed__30 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__30();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__30);
l_Lake_PackageEntry_fromJson_x3f___closed__31 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__31();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__31);
l_Lake_PackageEntry_fromJson_x3f___closed__32 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__32();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__32);
l_Lake_PackageEntry_fromJson_x3f___closed__33 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__33();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__33);
l_Lake_PackageEntry_fromJson_x3f___closed__34 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__34();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__34);
l_Lake_PackageEntry_fromJson_x3f___closed__35 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__35();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__35);
l_Lake_PackageEntry_fromJson_x3f___closed__36 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__36();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__36);
l_Lake_PackageEntry_fromJson_x3f___closed__37 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__37();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__37);
l_Lake_PackageEntry_fromJson_x3f___closed__38 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__38();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__38);
l_Lake_PackageEntry_fromJson_x3f___closed__39 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__39();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__39);
l_Lake_PackageEntry_fromJson_x3f___closed__40 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__40();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__40);
l_Lake_PackageEntry_fromJson_x3f___closed__41 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__41();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__41);
l_Lake_PackageEntry_fromJson_x3f___closed__42 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__42();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__42);
l_Lake_PackageEntry_fromJson_x3f___closed__43 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__43();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__43);
l_Lake_PackageEntry_fromJson_x3f___closed__44 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__44();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__44);
l_Lake_PackageEntry_fromJson_x3f___closed__45 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__45();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__45);
l_Lake_PackageEntry_fromJson_x3f___closed__46 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__46();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__46);
l_Lake_PackageEntry_fromJson_x3f___closed__47 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__47();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__47);
l_Lake_PackageEntry_instFromJson___closed__1 = _init_l_Lake_PackageEntry_instFromJson___closed__1();
lean_mark_persistent(l_Lake_PackageEntry_instFromJson___closed__1);
l_Lake_PackageEntry_instFromJson = _init_l_Lake_PackageEntry_instFromJson();
lean_mark_persistent(l_Lake_PackageEntry_instFromJson);
l_Lake_Manifest_toJson___closed__1 = _init_l_Lake_Manifest_toJson___closed__1();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__1);
l_Lake_Manifest_toJson___closed__2 = _init_l_Lake_Manifest_toJson___closed__2();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__2);
l_Lake_Manifest_toJson___closed__3 = _init_l_Lake_Manifest_toJson___closed__3();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__3);
l_Lake_Manifest_toJson___closed__4 = _init_l_Lake_Manifest_toJson___closed__4();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__4);
l_Lake_Manifest_toJson___closed__5 = _init_l_Lake_Manifest_toJson___closed__5();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__5);
l_Lake_Manifest_toJson___closed__6 = _init_l_Lake_Manifest_toJson___closed__6();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__6);
l_Lake_Manifest_toJson___closed__7 = _init_l_Lake_Manifest_toJson___closed__7();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__7);
l_Lake_Manifest_toJson___closed__8 = _init_l_Lake_Manifest_toJson___closed__8();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__8);
l_Lake_Manifest_instToJson___closed__1 = _init_l_Lake_Manifest_instToJson___closed__1();
lean_mark_persistent(l_Lake_Manifest_instToJson___closed__1);
l_Lake_Manifest_instToJson = _init_l_Lake_Manifest_instToJson();
lean_mark_persistent(l_Lake_Manifest_instToJson);
l_Lake_Manifest_getVersion___lambda__1___closed__1 = _init_l_Lake_Manifest_getVersion___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Manifest_getVersion___lambda__1___closed__1);
l_Lake_Manifest_getVersion___lambda__1___closed__2 = _init_l_Lake_Manifest_getVersion___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Manifest_getVersion___lambda__1___closed__2);
l_Lake_Manifest_getVersion___lambda__1___closed__3 = _init_l_Lake_Manifest_getVersion___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Manifest_getVersion___lambda__1___closed__3);
l_Lake_Manifest_getVersion___lambda__1___closed__4 = _init_l_Lake_Manifest_getVersion___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Manifest_getVersion___lambda__1___closed__4);
l_Lake_Manifest_getVersion___lambda__1___closed__5 = _init_l_Lake_Manifest_getVersion___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Manifest_getVersion___lambda__1___closed__5);
l_Lake_Manifest_getVersion___lambda__1___closed__6 = _init_l_Lake_Manifest_getVersion___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Manifest_getVersion___lambda__1___closed__6);
l_Lake_Manifest_getVersion___closed__1 = _init_l_Lake_Manifest_getVersion___closed__1();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__1);
l_Lake_Manifest_getVersion___closed__2 = _init_l_Lake_Manifest_getVersion___closed__2();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__2);
l_Lake_Manifest_getVersion___closed__3 = _init_l_Lake_Manifest_getVersion___closed__3();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__3);
l_Lake_Manifest_getVersion___closed__4 = _init_l_Lake_Manifest_getVersion___closed__4();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__4);
l_Lake_Manifest_getVersion___closed__5 = _init_l_Lake_Manifest_getVersion___closed__5();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__5);
l_Lake_Manifest_getVersion___closed__6 = _init_l_Lake_Manifest_getVersion___closed__6();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__6);
l_Lake_Manifest_getVersion___closed__7 = _init_l_Lake_Manifest_getVersion___closed__7();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__7);
l_Lake_Manifest_getPackages___closed__1 = _init_l_Lake_Manifest_getPackages___closed__1();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__1);
l_Lake_Manifest_getPackages___closed__2 = _init_l_Lake_Manifest_getPackages___closed__2();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__2);
l_Lake_Manifest_getPackages___closed__3 = _init_l_Lake_Manifest_getPackages___closed__3();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__3);
l_Lake_Manifest_getPackages___closed__4 = _init_l_Lake_Manifest_getPackages___closed__4();
l_Lake_Manifest_getPackages___closed__5 = _init_l_Lake_Manifest_getPackages___closed__5();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__5);
l_Lake_Manifest_getPackages___closed__6 = _init_l_Lake_Manifest_getPackages___closed__6();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__6);
l_Lake_Manifest_getPackages___closed__7 = _init_l_Lake_Manifest_getPackages___closed__7();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__7);
l_Lake_Manifest_getPackages___closed__8 = _init_l_Lake_Manifest_getPackages___closed__8();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__8);
l_Lake_Manifest_fromJson_x3f___closed__1 = _init_l_Lake_Manifest_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__1);
l_Lake_Manifest_fromJson_x3f___closed__2 = _init_l_Lake_Manifest_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__2);
l_Lake_Manifest_fromJson_x3f___closed__3 = _init_l_Lake_Manifest_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__3);
l_Lake_Manifest_fromJson_x3f___closed__4 = _init_l_Lake_Manifest_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__4);
l_Lake_Manifest_fromJson_x3f___closed__5 = _init_l_Lake_Manifest_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__5);
l_Lake_Manifest_instFromJson___closed__1 = _init_l_Lake_Manifest_instFromJson___closed__1();
lean_mark_persistent(l_Lake_Manifest_instFromJson___closed__1);
l_Lake_Manifest_instFromJson = _init_l_Lake_Manifest_instFromJson();
lean_mark_persistent(l_Lake_Manifest_instFromJson);
l_Lake_Manifest_parse___closed__1 = _init_l_Lake_Manifest_parse___closed__1();
lean_mark_persistent(l_Lake_Manifest_parse___closed__1);
l_Lake_Manifest_parse___closed__2 = _init_l_Lake_Manifest_parse___closed__2();
lean_mark_persistent(l_Lake_Manifest_parse___closed__2);
l_Lake_Manifest_saveEntries___closed__1 = _init_l_Lake_Manifest_saveEntries___closed__1();
lean_mark_persistent(l_Lake_Manifest_saveEntries___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
static lean_object* l_Lake_Manifest_version___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__27;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__33;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__5;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__31;
lean_object* l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instToJson;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__6;
static lean_object* l_Lake_PackageEntry_toJson___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__2;
static lean_object* l_Lake_Manifest_toJson___closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__7;
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__6;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_instFromJson___closed__1;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_Manifest_getPackages___spec__5(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_instInhabitedPackageEntryV6___closed__1;
static lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
uint8_t l_Ord_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_parse___closed__1;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__4;
static lean_object* l_Lake_PackageEntry_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__37;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__14;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__39;
static lean_object* l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
static lean_object* l_Lake_PackageEntry_toJson___closed__6;
static size_t l_Lake_Manifest_getPackages___closed__2;
static lean_object* l_Lake_Manifest_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedJson;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
static lean_object* l_Lake_Manifest_toJson___closed__3;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
static lean_object* l_Lake_Manifest_saveEntries___closed__1;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__2;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__1;
static lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
static lean_object* l_Lake_Manifest_version___closed__1;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__41;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__38;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__9;
static lean_object* l_Lake_instInhabitedPackageEntrySrc___closed__1;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__6;
static lean_object* l_Lake_Manifest_toJson___closed__5;
LEAN_EXPORT lean_object* l_Lake_Manifest_instFromJson;
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__2;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__32;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__3;
static lean_object* l_Lake_Manifest_parse___closed__2;
lean_object* l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__6;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__18;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__10;
static lean_object* l_Lake_PackageEntry_toJson___closed__9;
static lean_object* l_Lake_Manifest_getPackages___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__12;
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__28;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instFromJson;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__7(size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__5;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_Manifest_getPackages___spec__2(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__22;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__19;
static lean_object* l_Lake_Manifest_getVersion___lambda__1___closed__4;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__23;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__34;
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___lambda__1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__8;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lake_instToJsonPackageEntryV6;
static lean_object* l_Lake_Manifest_getPackages___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___boxed(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
static lean_object* l_Lake_instInhabitedPackageEntry___closed__1;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_Manifest_fromJson_x3f___spec__1(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__13;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_instToJson;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
static lean_object* l_Lake_PackageEntry_toJson___closed__10;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__24;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__12;
static lean_object* l_Lake_PackageEntry_toJson___closed__7;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__29;
static lean_object* l_Lake_Manifest_getVersion___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__4(size_t, size_t, lean_object*);
lean_object* l_Lake_StdVer_parse(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at_Lake_Manifest_toJson___spec__1(lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__4;
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
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
static lean_object* l_Lake_instToJsonPackageEntryV6___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__25;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__11;
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_Manifest_version___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
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
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__44;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Manifest_getVersion___closed__2;
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__4;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__43;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__4;
extern lean_object* l_Lake_defaultConfigFile;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__6(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__16;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntryV6;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__9;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__36;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__4;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__26;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__6;
static lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1;
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__21;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_instFromJsonPackageEntryV6___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__10;
static lean_object* l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1;
static lean_object* l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
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
static lean_object* _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2(x_1, x_4);
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1;
x_15 = lean_string_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_inc(x_5);
x_16 = l_String_toName(x_5);
x_17 = l_Lean_Name_isAnonymous(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_8);
lean_dec(x_5);
x_18 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_13, x_16, x_22);
x_1 = x_23;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
x_25 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2;
x_26 = lean_string_append(x_25, x_5);
lean_dec(x_5);
x_27 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_28);
return x_8;
}
}
else
{
lean_object* x_29; 
lean_free_object(x_8);
lean_dec(x_5);
x_29 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_13, x_34, x_33);
x_1 = x_35;
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec(x_8);
x_38 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1;
x_39 = lean_string_dec_eq(x_5, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_inc(x_5);
x_40 = l_String_toName(x_5);
x_41 = l_Lean_Name_isAnonymous(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_5);
x_42 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_7);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_37, x_40, x_46);
x_1 = x_47;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
x_49 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2;
x_50 = lean_string_append(x_49, x_5);
lean_dec(x_5);
x_51 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_5);
x_54 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_37);
lean_dec(x_7);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_37, x_59, x_58);
x_1 = x_60;
x_2 = x_7;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
x_4 = l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_1, x_9);
x_11 = l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2(x_17, x_16);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(80u);
lean_inc(x_1);
x_20 = l_Lean_Json_pretty(x_1, x_19);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
x_24 = lean_string_append(x_23, x_20);
lean_dec(x_20);
x_25 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_26 = lean_string_append(x_24, x_25);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_27 = l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1;
x_28 = lean_string_append(x_27, x_20);
lean_dec(x_20);
x_29 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Lean_Json_getStr_x3f(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
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
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev\?", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir\?", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__8;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__6;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__4;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__2;
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
x_20 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9;
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
x_24 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_28 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_29 = l_Except_orElseLazy___rarg(x_27, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_instInhabitedJson;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get(x_31, x_30, x_32);
x_34 = l_Lean_Name_fromJson_x3f(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_37 = l_Except_orElseLazy___rarg(x_34, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_41 = l_Except_orElseLazy___rarg(x_39, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_array_get(x_31, x_30, x_43);
x_45 = l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_42);
lean_dec(x_30);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_51 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_55 = lean_array_get(x_31, x_30, x_54);
x_56 = l_Lean_Json_getBool_x3f(x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_30);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_62 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_66 = lean_array_get(x_31, x_30, x_65);
x_67 = l_Lean_Json_getStr_x3f(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_30);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_73 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_77 = lean_array_get(x_31, x_30, x_76);
x_78 = l_Lean_Json_getStr_x3f(x_77);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_30);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
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
x_84 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_85 = l_Except_orElseLazy___rarg(x_83, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
lean_dec(x_78);
x_87 = lean_unsigned_to_nat(5u);
x_88 = lean_array_get(x_31, x_30, x_87);
x_89 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3(x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_30);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_92 = l_Except_orElseLazy___rarg(x_89, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_96 = l_Except_orElseLazy___rarg(x_94, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
lean_dec(x_89);
x_98 = lean_unsigned_to_nat(6u);
x_99 = lean_array_get(x_31, x_30, x_98);
lean_dec(x_30);
x_100 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_99);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
lean_dec(x_97);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_42);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_103 = l_Except_orElseLazy___rarg(x_100, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_107 = l_Except_orElseLazy___rarg(x_105, x_106);
return x_107;
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_100, 0);
x_110 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_110, 0, x_42);
lean_ctor_set(x_110, 1, x_53);
lean_ctor_set(x_110, 2, x_75);
lean_ctor_set(x_110, 3, x_86);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_109);
x_111 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_110, sizeof(void*)*6, x_111);
lean_ctor_set(x_100, 0, x_110);
x_112 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_113 = l_Except_orElseLazy___rarg(x_100, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_100, 0);
lean_inc(x_114);
lean_dec(x_100);
x_115 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_115, 0, x_42);
lean_ctor_set(x_115, 1, x_53);
lean_ctor_set(x_115, 2, x_75);
lean_ctor_set(x_115, 3, x_86);
lean_ctor_set(x_115, 4, x_97);
lean_ctor_set(x_115, 5, x_114);
x_116 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_115, sizeof(void*)*6, x_116);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_115);
x_118 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10;
x_119 = l_Except_orElseLazy___rarg(x_117, x_118);
return x_119;
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
x_10 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___boxed), 6, 5);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_instInhabitedJson;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
x_20 = l_Lean_Name_fromJson_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Except_orElseLazy___rarg(x_20, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___rarg(x_24, x_10);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_get(x_17, x_16, x_27);
x_29 = l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_26);
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
x_37 = lean_array_get(x_17, x_16, x_36);
x_38 = l_Lean_Json_getBool_x3f(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_26);
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
x_46 = lean_array_get(x_17, x_16, x_45);
lean_dec(x_16);
x_47 = l_Lean_Json_getStr_x3f(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_44);
lean_dec(x_35);
lean_dec(x_26);
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
lean_ctor_set(x_55, 0, x_26);
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
lean_ctor_set(x_59, 0, x_26);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(x_1, x_3);
x_8 = 1;
x_9 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2(x_2, x_1);
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lake_mkRelPathString(x_4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lake_mkRelPathString(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 1;
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_8 = l_Lean_Name_toString(x_2, x_6, x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_NameMap_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(x_3);
x_13 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_15, 0, x_4);
x_16 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lake_mkRelPathString(x_5);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
x_31 = l_Lean_Json_mkObj(x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 5);
lean_inc(x_38);
lean_dec(x_1);
x_39 = 1;
x_40 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_41 = l_Lean_Name_toString(x_32, x_39, x_40);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_NameMap_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__1(x_33);
x_46 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__3;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_48, 0, x_34);
x_49 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_35);
x_52 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_36);
x_55 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(x_37);
x_58 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(x_38);
x_61 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_47);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_44);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Json_mkObj(x_70);
x_72 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_63);
x_75 = l_Lean_Json_mkObj(x_74);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___lambda__1(x_1);
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
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
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
x_19 = l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(x_18);
x_20 = l_Lake_PackageEntry_toJson___closed__3;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_23 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_23, 0, x_22);
x_24 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_1, 4);
lean_inc(x_32);
lean_dec(x_1);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lake_mkRelPathString(x_34);
lean_ctor_set_tag(x_32, 3);
lean_ctor_set(x_32, 0, x_35);
x_36 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
x_39 = l_List_appendTR___rarg(x_31, x_38);
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
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = l_Lake_mkRelPathString(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_26);
x_49 = l_List_appendTR___rarg(x_31, x_48);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_32, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_32, 3);
lean_inc(x_56);
lean_dec(x_32);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_53);
x_58 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_54);
x_61 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__3(x_55);
x_64 = l_Lake_PackageEntry_toJson___closed__9;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(x_56);
x_67 = l_Lake_PackageEntry_toJson___closed__10;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_26);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_List_appendTR___rarg(x_31, x_72);
x_74 = l_Lake_PackageEntry_toJson___closed__8;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Json_mkObj(x_75);
return x_76;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package entry: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__3;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__5;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__8;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package entry '", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__13;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__15;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__17;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
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
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown package entry type '", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__22;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__24;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__28;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__30;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__32;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__34;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
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
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultManifestFile;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__39;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__41;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_PackageEntry_toJson___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__43;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lake_Manifest_version___closed__2;
x_8 = lean_string_append(x_6, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_Manifest_version___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_17 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = l_Lake_PackageEntry_fromJson_x3f___closed__7;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Name_fromJson_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lake_PackageEntry_fromJson_x3f___closed__10;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lake_Manifest_version___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_28, x_25);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lake_PackageEntry_fromJson_x3f___closed__10;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lake_Manifest_version___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = lean_string_append(x_36, x_33);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_54; lean_object* x_290; lean_object* x_291; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_40 = x_20;
} else {
 lean_dec_ref(x_20);
 x_40 = lean_box(0);
}
x_290 = l_Lake_PackageEntry_toJson___closed__1;
x_291 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = l_Lake_Manifest_version___closed__2;
x_54 = x_292;
goto block_289;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3(x_293);
if (lean_obj_tag(x_294) == 0)
{
uint8_t x_295; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_15);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = l_Lake_PackageEntry_fromJson_x3f___closed__44;
x_298 = lean_string_append(x_297, x_296);
lean_dec(x_296);
x_299 = l_Lake_Manifest_version___closed__2;
x_300 = lean_string_append(x_298, x_299);
lean_ctor_set(x_294, 0, x_300);
return x_294;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_301 = lean_ctor_get(x_294, 0);
lean_inc(x_301);
lean_dec(x_294);
x_302 = l_Lake_PackageEntry_fromJson_x3f___closed__44;
x_303 = lean_string_append(x_302, x_301);
lean_dec(x_301);
x_304 = l_Lake_Manifest_version___closed__2;
x_305 = lean_string_append(x_303, x_304);
x_306 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_306, 0, x_305);
return x_306;
}
}
else
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_294, 0);
lean_inc(x_307);
lean_dec(x_294);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = l_Lake_Manifest_version___closed__2;
x_54 = x_308;
goto block_289;
}
else
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
lean_dec(x_307);
x_54 = x_309;
goto block_289;
}
}
}
block_53:
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = 1;
x_43 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
x_44 = l_Lean_Name_toString(x_39, x_42, x_43);
x_45 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lake_PackageEntry_fromJson_x3f___closed__12;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_41);
lean_dec(x_41);
x_50 = l_Lake_Manifest_version___closed__2;
x_51 = lean_string_append(x_49, x_50);
if (lean_is_scalar(x_40)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_40;
 lean_ctor_set_tag(x_52, 0);
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
block_289:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lake_PackageEntry_toJson___closed__5;
x_56 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_15);
x_57 = l_Lake_PackageEntry_fromJson_x3f___closed__14;
x_41 = x_57;
goto block_53;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Json_getStr_x3f(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
lean_dec(x_15);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lake_PackageEntry_fromJson_x3f___closed__16;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lake_Manifest_version___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_41 = x_64;
goto block_53;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__5;
x_67 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_15);
x_68 = l_Lake_PackageEntry_fromJson_x3f___closed__18;
x_41 = x_68;
goto block_53;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Json_getBool_x3f(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_15);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lake_PackageEntry_fromJson_x3f___closed__20;
x_74 = lean_string_append(x_73, x_72);
lean_dec(x_72);
x_75 = l_Lake_Manifest_version___closed__2;
x_76 = lean_string_append(x_74, x_75);
x_41 = x_76;
goto block_53;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_276; lean_object* x_277; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
x_276 = l_Lake_PackageEntry_toJson___closed__2;
x_277 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = l_Lake_defaultConfigFile;
x_79 = x_278;
goto block_275;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_15);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec(x_280);
x_282 = l_Lake_PackageEntry_fromJson_x3f___closed__42;
x_283 = lean_string_append(x_282, x_281);
lean_dec(x_281);
x_284 = l_Lake_Manifest_version___closed__2;
x_285 = lean_string_append(x_283, x_284);
x_41 = x_285;
goto block_53;
}
else
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_280, 0);
lean_inc(x_286);
lean_dec(x_280);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
x_287 = l_Lake_defaultConfigFile;
x_79 = x_287;
goto block_275;
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
lean_dec(x_286);
x_79 = x_288;
goto block_275;
}
}
}
block_275:
{
lean_object* x_80; lean_object* x_157; lean_object* x_158; 
x_157 = l_Lake_PackageEntry_toJson___closed__3;
x_158 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_78);
lean_dec(x_70);
x_159 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_160 = lean_string_dec_eq(x_65, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9;
x_162 = lean_string_dec_eq(x_65, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
lean_dec(x_15);
x_163 = l_Lake_PackageEntry_fromJson_x3f___closed__21;
x_164 = lean_string_append(x_163, x_65);
lean_dec(x_65);
x_165 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_166 = lean_string_append(x_164, x_165);
x_41 = x_166;
goto block_53;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_65);
x_167 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_168 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
lean_dec(x_15);
x_169 = l_Lake_PackageEntry_fromJson_x3f___closed__23;
x_41 = x_169;
goto block_53;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Json_getStr_x3f(x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
lean_dec(x_15);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lake_PackageEntry_fromJson_x3f___closed__25;
x_174 = lean_string_append(x_173, x_172);
lean_dec(x_172);
x_175 = l_Lake_Manifest_version___closed__2;
x_176 = lean_string_append(x_174, x_175);
x_41 = x_176;
goto block_53;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
lean_dec(x_171);
x_178 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
x_179 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
lean_dec(x_177);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
lean_dec(x_15);
x_180 = l_Lake_PackageEntry_fromJson_x3f___closed__27;
x_41 = x_180;
goto block_53;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Json_getStr_x3f(x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_177);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
lean_dec(x_15);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lake_PackageEntry_fromJson_x3f___closed__29;
x_185 = lean_string_append(x_184, x_183);
lean_dec(x_183);
x_186 = l_Lake_Manifest_version___closed__2;
x_187 = lean_string_append(x_185, x_186);
x_41 = x_187;
goto block_53;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_219; lean_object* x_220; 
x_188 = lean_ctor_get(x_182, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_189 = x_182;
} else {
 lean_dec_ref(x_182);
 x_189 = lean_box(0);
}
x_219 = l_Lake_PackageEntry_toJson___closed__9;
x_220 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_box(0);
x_190 = x_221;
goto block_218;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3(x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_177);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
lean_dec(x_15);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec(x_223);
x_225 = l_Lake_PackageEntry_fromJson_x3f___closed__33;
x_226 = lean_string_append(x_225, x_224);
lean_dec(x_224);
x_227 = l_Lake_Manifest_version___closed__2;
x_228 = lean_string_append(x_226, x_227);
x_41 = x_228;
goto block_53;
}
else
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_223, 0);
lean_inc(x_229);
lean_dec(x_223);
x_190 = x_229;
goto block_218;
}
}
block_218:
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Lake_PackageEntry_toJson___closed__10;
x_192 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_191);
lean_dec(x_15);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
lean_dec(x_40);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_194, 0, x_177);
lean_ctor_set(x_194, 1, x_188);
lean_ctor_set(x_194, 2, x_190);
lean_ctor_set(x_194, 3, x_193);
x_195 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_196 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_196, 0, x_39);
lean_ctor_set(x_196, 1, x_54);
lean_ctor_set(x_196, 2, x_79);
lean_ctor_set(x_196, 3, x_195);
lean_ctor_set(x_196, 4, x_194);
x_197 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_196, sizeof(void*)*5, x_197);
if (lean_is_scalar(x_189)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_189;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_189);
x_199 = lean_ctor_get(x_192, 0);
lean_inc(x_199);
lean_dec(x_192);
x_200 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_177);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = l_Lake_PackageEntry_fromJson_x3f___closed__31;
x_203 = lean_string_append(x_202, x_201);
lean_dec(x_201);
x_204 = l_Lake_Manifest_version___closed__2;
x_205 = lean_string_append(x_203, x_204);
x_41 = x_205;
goto block_53;
}
else
{
uint8_t x_206; 
lean_dec(x_40);
x_206 = !lean_is_exclusive(x_200);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_200, 0);
x_208 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_208, 0, x_177);
lean_ctor_set(x_208, 1, x_188);
lean_ctor_set(x_208, 2, x_190);
lean_ctor_set(x_208, 3, x_207);
x_209 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_210 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_210, 0, x_39);
lean_ctor_set(x_210, 1, x_54);
lean_ctor_set(x_210, 2, x_79);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set(x_210, 4, x_208);
x_211 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_210, sizeof(void*)*5, x_211);
lean_ctor_set(x_200, 0, x_210);
return x_200;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_200, 0);
lean_inc(x_212);
lean_dec(x_200);
x_213 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_213, 0, x_177);
lean_ctor_set(x_213, 1, x_188);
lean_ctor_set(x_213, 2, x_190);
lean_ctor_set(x_213, 3, x_212);
x_214 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_215 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_215, 0, x_39);
lean_ctor_set(x_215, 1, x_54);
lean_ctor_set(x_215, 2, x_79);
lean_ctor_set(x_215, 3, x_214);
lean_ctor_set(x_215, 4, x_213);
x_216 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_215, sizeof(void*)*5, x_216);
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_215);
return x_217;
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
lean_object* x_230; lean_object* x_231; 
lean_dec(x_65);
x_230 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_231 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_230);
lean_dec(x_15);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
x_232 = l_Lake_PackageEntry_fromJson_x3f___closed__35;
x_41 = x_232;
goto block_53;
}
else
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_231, 0);
x_235 = l_Lean_Json_getStr_x3f(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_231);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec(x_235);
x_237 = l_Lake_PackageEntry_fromJson_x3f___closed__37;
x_238 = lean_string_append(x_237, x_236);
lean_dec(x_236);
x_239 = l_Lake_Manifest_version___closed__2;
x_240 = lean_string_append(x_238, x_239);
x_41 = x_240;
goto block_53;
}
else
{
uint8_t x_241; 
lean_dec(x_40);
x_241 = !lean_is_exclusive(x_235);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_235, 0);
lean_ctor_set_tag(x_231, 0);
lean_ctor_set(x_231, 0, x_242);
x_243 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_244 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_244, 0, x_39);
lean_ctor_set(x_244, 1, x_54);
lean_ctor_set(x_244, 2, x_79);
lean_ctor_set(x_244, 3, x_243);
lean_ctor_set(x_244, 4, x_231);
x_245 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_244, sizeof(void*)*5, x_245);
lean_ctor_set(x_235, 0, x_244);
return x_235;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_235, 0);
lean_inc(x_246);
lean_dec(x_235);
lean_ctor_set_tag(x_231, 0);
lean_ctor_set(x_231, 0, x_246);
x_247 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_248 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_248, 0, x_39);
lean_ctor_set(x_248, 1, x_54);
lean_ctor_set(x_248, 2, x_79);
lean_ctor_set(x_248, 3, x_247);
lean_ctor_set(x_248, 4, x_231);
x_249 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_248, sizeof(void*)*5, x_249);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_248);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_231, 0);
lean_inc(x_251);
lean_dec(x_231);
x_252 = l_Lean_Json_getStr_x3f(x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_54);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lake_PackageEntry_fromJson_x3f___closed__37;
x_255 = lean_string_append(x_254, x_253);
lean_dec(x_253);
x_256 = l_Lake_Manifest_version___closed__2;
x_257 = lean_string_append(x_255, x_256);
x_41 = x_257;
goto block_53;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; 
lean_dec(x_40);
x_258 = lean_ctor_get(x_252, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_259 = x_252;
} else {
 lean_dec_ref(x_252);
 x_259 = lean_box(0);
}
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_258);
x_261 = l_Lake_PackageEntry_fromJson_x3f___closed__38;
x_262 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_262, 0, x_39);
lean_ctor_set(x_262, 1, x_54);
lean_ctor_set(x_262, 2, x_79);
lean_ctor_set(x_262, 3, x_261);
lean_ctor_set(x_262, 4, x_260);
x_263 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_262, sizeof(void*)*5, x_263);
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_259;
}
lean_ctor_set(x_264, 0, x_262);
return x_264;
}
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_158, 0);
lean_inc(x_265);
lean_dec(x_158);
x_266 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_15);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_Lake_PackageEntry_fromJson_x3f___closed__40;
x_269 = lean_string_append(x_268, x_267);
lean_dec(x_267);
x_270 = l_Lake_Manifest_version___closed__2;
x_271 = lean_string_append(x_269, x_270);
x_41 = x_271;
goto block_53;
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_266, 0);
lean_inc(x_272);
lean_dec(x_266);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = l_Lake_defaultManifestFile;
x_80 = x_273;
goto block_156;
}
else
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
lean_dec(x_272);
x_80 = x_274;
goto block_156;
}
}
}
block_156:
{
lean_object* x_81; lean_object* x_87; uint8_t x_88; 
x_87 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__15;
x_88 = lean_string_dec_eq(x_65, x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9;
x_90 = lean_string_dec_eq(x_65, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
lean_dec(x_15);
x_91 = l_Lake_PackageEntry_fromJson_x3f___closed__21;
x_92 = lean_string_append(x_91, x_65);
lean_dec(x_65);
x_93 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_94 = lean_string_append(x_92, x_93);
x_41 = x_94;
goto block_53;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_65);
x_95 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1;
x_96 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
lean_dec(x_15);
x_97 = l_Lake_PackageEntry_fromJson_x3f___closed__23;
x_41 = x_97;
goto block_53;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Json_getStr_x3f(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
lean_dec(x_15);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lake_PackageEntry_fromJson_x3f___closed__25;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = l_Lake_Manifest_version___closed__2;
x_104 = lean_string_append(x_102, x_103);
x_41 = x_104;
goto block_53;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
lean_dec(x_99);
x_106 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3;
x_107 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
lean_dec(x_15);
x_108 = l_Lake_PackageEntry_fromJson_x3f___closed__27;
x_41 = x_108;
goto block_53;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Json_getStr_x3f(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_105);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
lean_dec(x_15);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lake_PackageEntry_fromJson_x3f___closed__29;
x_113 = lean_string_append(x_112, x_111);
lean_dec(x_111);
x_114 = l_Lake_Manifest_version___closed__2;
x_115 = lean_string_append(x_113, x_114);
x_41 = x_115;
goto block_53;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_132; lean_object* x_133; 
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
lean_dec(x_110);
x_132 = l_Lake_PackageEntry_toJson___closed__9;
x_133 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_117 = x_134;
goto block_131;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_116);
lean_dec(x_105);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
lean_dec(x_15);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lake_PackageEntry_fromJson_x3f___closed__33;
x_139 = lean_string_append(x_138, x_137);
lean_dec(x_137);
x_140 = l_Lake_Manifest_version___closed__2;
x_141 = lean_string_append(x_139, x_140);
x_41 = x_141;
goto block_53;
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_136, 0);
lean_inc(x_142);
lean_dec(x_136);
x_117 = x_142;
goto block_131;
}
}
block_131:
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lake_PackageEntry_toJson___closed__10;
x_119 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_118);
lean_dec(x_15);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_40);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_117);
lean_ctor_set(x_121, 3, x_120);
x_81 = x_121;
goto block_86;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_dec(x_119);
x_123 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_105);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec(x_123);
x_125 = l_Lake_PackageEntry_fromJson_x3f___closed__31;
x_126 = lean_string_append(x_125, x_124);
lean_dec(x_124);
x_127 = l_Lake_Manifest_version___closed__2;
x_128 = lean_string_append(x_126, x_127);
x_41 = x_128;
goto block_53;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_40);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
lean_dec(x_123);
x_130 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_130, 0, x_105);
lean_ctor_set(x_130, 1, x_116);
lean_ctor_set(x_130, 2, x_117);
lean_ctor_set(x_130, 3, x_129);
x_81 = x_130;
goto block_86;
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
lean_object* x_143; lean_object* x_144; 
lean_dec(x_65);
x_143 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__7;
x_144 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_143);
lean_dec(x_15);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
x_145 = l_Lake_PackageEntry_fromJson_x3f___closed__35;
x_41 = x_145;
goto block_53;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Json_getStr_x3f(x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_54);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lake_PackageEntry_fromJson_x3f___closed__37;
x_150 = lean_string_append(x_149, x_148);
lean_dec(x_148);
x_151 = l_Lake_Manifest_version___closed__2;
x_152 = lean_string_append(x_150, x_151);
x_41 = x_152;
goto block_53;
}
else
{
uint8_t x_153; 
lean_dec(x_40);
x_153 = !lean_is_exclusive(x_147);
if (x_153 == 0)
{
lean_ctor_set_tag(x_147, 0);
x_81 = x_147;
goto block_86;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_147, 0);
lean_inc(x_154);
lean_dec(x_147);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_81 = x_155;
goto block_86;
}
}
}
}
block_86:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
if (lean_is_scalar(x_70)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_70;
}
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_54);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_81);
x_84 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_84);
if (lean_is_scalar(x_78)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_78;
}
lean_ctor_set(x_85, 0, x_83);
return x_85;
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
x_8 = l_Lake_joinRelative(x_1, x_7);
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
x_10 = l_Lake_joinRelative(x_1, x_9);
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
x_19 = l_Lake_joinRelative(x_1, x_17);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_toJson___at_Lake_Manifest_toJson___spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__2(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
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
x_1 = lean_mk_string_unchecked("packagesDir", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packages", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1;
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
x_15 = l_Option_toJson___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__4(x_14);
x_16 = l_Lake_Manifest_toJson___closed__6;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Array_toJson___at_Lake_Manifest_toJson___spec__1(x_18);
x_20 = l_Lake_Manifest_toJson___closed__7;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lake_Manifest_toJson___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__2(x_4, x_5, x_3);
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
x_13 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
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
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_1, x_9);
x_11 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 4:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__4(x_17, x_18, x_16);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(80u);
lean_inc(x_1);
x_21 = l_Lean_Json_pretty(x_1, x_20);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_25 = lean_string_append(x_24, x_21);
lean_dec(x_21);
x_26 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_28 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_29 = lean_string_append(x_28, x_21);
lean_dec(x_21);
x_30 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_Manifest_getPackages___spec__2(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__6(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_1, x_9);
x_11 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 4:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__7(x_17, x_18, x_16);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(80u);
lean_inc(x_1);
x_21 = l_Lean_Json_pretty(x_1, x_20);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_25 = lean_string_append(x_24, x_21);
lean_dec(x_21);
x_26 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_28 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1;
x_29 = lean_string_append(x_28, x_21);
lean_dec(x_21);
x_30 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_Manifest_getPackages___spec__5(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__6(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__6(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lake_Manifest_getPackages___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_Manifest_getPackages___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__3() {
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
static lean_object* _init_l_Lake_Manifest_getPackages___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getPackages___closed__3;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_getPackages___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_getPackages___closed__6;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lake_instOrdStdVer;
x_21 = l_Lake_Manifest_getPackages___closed__4;
x_22 = l_Ord_instDecidableRelLt___rarg(x_20, x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lake_Manifest_toJson___closed__7;
x_24 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lake_Manifest_getPackages___closed__5;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Option_fromJson_x3f___at_Lake_Manifest_getPackages___spec__2(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lake_Manifest_getPackages___closed__7;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lake_Manifest_version___closed__2;
x_33 = lean_string_append(x_31, x_32);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lake_Manifest_getPackages___closed__7;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lake_Manifest_version___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_free_object(x_27);
x_42 = l_Lake_Manifest_getPackages___closed__5;
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_ctor_set(x_27, 0, x_43);
return x_27;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = l_Lake_Manifest_getPackages___closed__5;
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lake_Manifest_toJson___closed__7;
x_49 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_2, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_3 = x_50;
goto block_19;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Option_fromJson_x3f___at_Lake_Manifest_getPackages___spec__5(x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = l_Lake_Manifest_getPackages___closed__7;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lake_Manifest_version___closed__2;
x_58 = lean_string_append(x_56, x_57);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = l_Lake_Manifest_getPackages___closed__7;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Lake_Manifest_version___closed__2;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
lean_dec(x_52);
x_3 = x_65;
goto block_19;
}
}
}
block_19:
{
if (lean_obj_tag(x_3) == 0)
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = 0;
x_5 = l_Lake_Manifest_getPackages___closed__2;
x_6 = l_Lake_Manifest_getPackages___closed__1;
x_7 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_5, x_4, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_11, x_12, x_10);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__1(x_15, x_16, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_getPackages___spec__7(x_4, x_5, x_3);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_Manifest_fromJson_x3f___spec__1(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Name_fromJson_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Lean_Name_fromJson_x3f(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___closed__1;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* x_1) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_78; lean_object* x_79; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_78 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____closed__1;
x_79 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_6, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_box(0);
x_12 = x_80;
goto block_77;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Option_fromJson_x3f___at_Lake_Manifest_fromJson_x3f___spec__1(x_81);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_11);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = l_Lake_PackageEntry_fromJson_x3f___closed__10;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = l_Lake_Manifest_version___closed__2;
x_88 = lean_string_append(x_86, x_87);
lean_ctor_set(x_82, 0, x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
lean_dec(x_82);
x_90 = l_Lake_PackageEntry_fromJson_x3f___closed__10;
x_91 = lean_string_append(x_90, x_89);
lean_dec(x_89);
x_92 = l_Lake_Manifest_version___closed__2;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
lean_dec(x_82);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_box(0);
x_12 = x_96;
goto block_77;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_12 = x_97;
goto block_77;
}
}
}
block_77:
{
lean_object* x_13; lean_object* x_57; lean_object* x_58; 
x_57 = l_Lake_Manifest_toJson___closed__5;
x_58 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_6, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = l_Lake_defaultLakeDir;
x_13 = x_59;
goto block_56;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = l_Lake_Manifest_version___closed__2;
x_67 = lean_string_append(x_65, x_66);
lean_ctor_set(x_61, 0, x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lake_Manifest_version___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = l_Lake_defaultLakeDir;
x_13 = x_75;
goto block_56;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_13 = x_76;
goto block_56;
}
}
}
block_56:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lake_Manifest_toJson___closed__6;
x_15 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = l_Lake_Manifest_version___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_Manifest_getPackages(x_18, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_16);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593____spec__2(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lake_Manifest_fromJson_x3f___closed__2;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lake_Manifest_version___closed__2;
x_36 = lean_string_append(x_34, x_35);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Lake_Manifest_fromJson_x3f___closed__2;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lake_Manifest_version___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = l_Lake_Manifest_version___closed__2;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_Manifest_getPackages(x_45, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_12);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_13);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_12);
lean_ctor_set(x_54, 1, x_13);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
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
x_15 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_36 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_43 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_60 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_72 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_27 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_38 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_50 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_58 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_15 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_36 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_43 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_60 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_72 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_68 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_79 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_91 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_99 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_7 = l_Lake_Manifest_getPackages___closed__1;
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
x_11 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_32 = l_Lake_Manifest_getPackages___closed__1;
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
x_36 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
x_46 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Array_toJson___at_Lake_Manifest_toJson___spec__1(x_2);
x_5 = l_Lake_Manifest_toJson___closed__7;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_Manifest_saveEntries___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Json_mkObj(x_10);
x_12 = lean_unsigned_to_nat(80u);
x_13 = l_Lean_Json_pretty(x_11, x_12);
x_14 = 10;
x_15 = lean_string_push(x_13, x_14);
x_16 = l_IO_FS_writeFile(x_1, x_15, x_3);
lean_dec(x_15);
return x_16;
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
l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1 = _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__1);
l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2 = _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__2);
l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3 = _init_l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3();
lean_mark_persistent(l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__2___closed__3);
l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1 = _init_l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1();
lean_mark_persistent(l_Lean_NameMap_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1___closed__1);
l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1 = _init_l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1();
lean_mark_persistent(l_Option_fromJson_x3f___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__3___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__1___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__3);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__4 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__4();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__4);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__5);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__6 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__6();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__6);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__7);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__8 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__8();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__8);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__9);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____lambda__2___closed__10);
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
l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1 = _init_l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456____spec__2___closed__1);
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
l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1 = _init_l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at_Lake_Manifest_getPackages___spec__3___closed__1);
l_Lake_Manifest_getPackages___closed__1 = _init_l_Lake_Manifest_getPackages___closed__1();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__1);
l_Lake_Manifest_getPackages___closed__2 = _init_l_Lake_Manifest_getPackages___closed__2();
l_Lake_Manifest_getPackages___closed__3 = _init_l_Lake_Manifest_getPackages___closed__3();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__3);
l_Lake_Manifest_getPackages___closed__4 = _init_l_Lake_Manifest_getPackages___closed__4();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__4);
l_Lake_Manifest_getPackages___closed__5 = _init_l_Lake_Manifest_getPackages___closed__5();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__5);
l_Lake_Manifest_getPackages___closed__6 = _init_l_Lake_Manifest_getPackages___closed__6();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__6);
l_Lake_Manifest_getPackages___closed__7 = _init_l_Lake_Manifest_getPackages___closed__7();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__7);
l_Lake_Manifest_fromJson_x3f___closed__1 = _init_l_Lake_Manifest_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__1);
l_Lake_Manifest_fromJson_x3f___closed__2 = _init_l_Lake_Manifest_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__2);
l_Lake_Manifest_fromJson_x3f___closed__3 = _init_l_Lake_Manifest_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__3);
l_Lake_Manifest_fromJson_x3f___closed__4 = _init_l_Lake_Manifest_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__4);
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

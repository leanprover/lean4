// Lean compiler output
// Module: Lake.Load.Manifest
// Imports: Init Lake.Util.Log Lake.Util.Name Lake.Util.FilePath Lake.Util.JsonObject Lake.Util.Version Lake.Load.Config Lake.Config.Workspace
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
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__42;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_version___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__27;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__46;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__33;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__5;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__2;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__31;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instToJson;
static lean_object* l_Lake_PackageEntry_toJson___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__2;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
static lean_object* l_Lake_Manifest_toJson___closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__12;
static lean_object* l_Lake_Manifest_toJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__4(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__9;
static lean_object* l_Lake_Manifest_toJson___closed__6;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__12;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__13;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__30;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__2(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_instFromJson___closed__1;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_instInhabitedPackageEntryV6___closed__1;
static lean_object* l_Lake_Manifest_parse___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__37;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__39;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__8;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
LEAN_EXPORT lean_object* l_Lake_Manifest_packages___default;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__9;
static lean_object* l_Lake_PackageEntry_toJson___closed__6;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
static lean_object* l_Lake_Manifest_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedJson;
static lean_object* l_Lake_Manifest_toJson___closed__3;
uint8_t l_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
static lean_object* l_Lake_PackageEntry_toJson___closed__2;
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___lambda__1(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__47;
static lean_object* l_Lake_Manifest_version___closed__1;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__5;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__41;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__38;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__9;
static lean_object* l_Lake_Manifest_packages___default___closed__1;
static lean_object* l_Lake_instInhabitedPackageEntrySrc___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__5;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__11;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__2;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6;
LEAN_EXPORT lean_object* l_Lake_Manifest_instFromJson;
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__45;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__32;
static size_t l_Lake_Manifest_fromJson_x3f___lambda__2___closed__7;
static lean_object* l_Lake_PackageEntry_toJson___closed__3;
static lean_object* l_Lake_Manifest_parse___closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__18;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__10;
static lean_object* l_Lake_PackageEntry_toJson___closed__9;
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__14;
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__28;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instFromJson;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__5;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__22;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__19;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__23;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__34;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
static lean_object* l_Lake_PackageEntry_toJson___closed__8;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lake_instToJsonPackageEntryV6;
static lean_object* l_Lake_instInhabitedPackageEntry___closed__1;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__4;
static lean_object* l_Lake_Manifest_toJson___closed__8;
extern lean_object* l_Lake_defaultLakeDir;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__2;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__14;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__2;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_instToJson;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__6;
static lean_object* l_Lake_PackageEntry_toJson___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3(size_t, size_t, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__24;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__3;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__8;
LEAN_EXPORT lean_object* l_Lake_Manifest_packagesDir_x3f___default;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__12;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15;
static lean_object* l_Lake_PackageEntry_toJson___closed__7;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__1;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__15;
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__29;
lean_object* l_Lake_StdVer_parse(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__11;
static lean_object* l_Lake_PackageEntry_toJson___closed__4;
static lean_object* l_Lake_PackageEntry_toJson___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonPackageEntryV6;
extern lean_object* l_Lake_instOrdStdVer;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__13;
static lean_object* l_Lake_instToJsonPackageEntryV6___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__25;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_configFile___default;
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460_(lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__12;
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_Manifest_version___closed__3;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10;
lean_object* l_Lean_Json_Parser_any(lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_manifestFile_x3f___default;
lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__40;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__9;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__11;
static lean_object* l_Lake_Manifest_instFromJson___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__17;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__35;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_scope___default;
LEAN_EXPORT lean_object* l_Lake_Manifest_version;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__15;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Manifest_toJson___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_toJson___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__44;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__43;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__4;
extern lean_object* l_Lake_defaultConfigFile;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__16;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntryV6;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___boxed(lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__5;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__36;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__4;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__26;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__14;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__10;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__21;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_instFromJsonPackageEntryV6___closed__1;
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__8;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__2;
extern lean_object* l_Lake_defaultManifestFile;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__13;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__6;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___closed__16;
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
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev\?", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir\?", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__9;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_2);
x_9 = lean_array_push(x_8, x_3);
x_10 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__2;
x_11 = lean_array_push(x_9, x_10);
x_12 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__4;
x_13 = lean_array_push(x_11, x_12);
x_14 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__6;
x_15 = lean_array_push(x_13, x_14);
x_16 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__8;
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
x_20 = lean_unsigned_to_nat(7u);
x_21 = l_Lean_Json_parseTagged(x_4, x_19, x_20, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_24 = l_Except_orElseLazy___rarg(x_21, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_28 = l_Except_orElseLazy___rarg(x_26, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_328 = lean_array_get_size(x_29);
x_329 = lean_unsigned_to_nat(0u);
x_330 = lean_nat_dec_lt(x_329, x_328);
lean_dec(x_328);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = l_Lean_instInhabitedJson;
x_332 = l_outOfBounds___rarg(x_331);
lean_inc(x_332);
x_333 = l_Lean_Json_getStr_x3f(x_332);
if (lean_obj_tag(x_333) == 0)
{
uint8_t x_334; 
lean_dec(x_332);
lean_dec(x_29);
x_334 = !lean_is_exclusive(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_336 = l_Except_orElseLazy___rarg(x_333, x_335);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_333, 0);
lean_inc(x_337);
lean_dec(x_333);
x_338 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_339 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_340 = l_Except_orElseLazy___rarg(x_338, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_333);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_333, 0);
x_343 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_344 = lean_string_dec_eq(x_342, x_343);
if (x_344 == 0)
{
lean_object* x_345; uint8_t x_346; 
x_345 = l_String_toName(x_342);
x_346 = l_Lean_Name_isAnonymous(x_345);
if (x_346 == 0)
{
lean_free_object(x_333);
lean_dec(x_332);
x_30 = x_345;
goto block_327;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_345);
lean_dec(x_29);
x_347 = lean_unsigned_to_nat(80u);
x_348 = l_Lean_Json_pretty(x_332, x_347);
x_349 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_350 = lean_string_append(x_349, x_348);
lean_dec(x_348);
x_351 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_352 = lean_string_append(x_350, x_351);
lean_ctor_set_tag(x_333, 0);
lean_ctor_set(x_333, 0, x_352);
x_353 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_354 = l_Except_orElseLazy___rarg(x_333, x_353);
return x_354;
}
}
else
{
lean_object* x_355; 
lean_free_object(x_333);
lean_dec(x_342);
lean_dec(x_332);
x_355 = lean_box(0);
x_30 = x_355;
goto block_327;
}
}
else
{
lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_356 = lean_ctor_get(x_333, 0);
lean_inc(x_356);
lean_dec(x_333);
x_357 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_358 = lean_string_dec_eq(x_356, x_357);
if (x_358 == 0)
{
lean_object* x_359; uint8_t x_360; 
x_359 = l_String_toName(x_356);
x_360 = l_Lean_Name_isAnonymous(x_359);
if (x_360 == 0)
{
lean_dec(x_332);
x_30 = x_359;
goto block_327;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_359);
lean_dec(x_29);
x_361 = lean_unsigned_to_nat(80u);
x_362 = l_Lean_Json_pretty(x_332, x_361);
x_363 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_364 = lean_string_append(x_363, x_362);
lean_dec(x_362);
x_365 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_366 = lean_string_append(x_364, x_365);
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_368 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_369 = l_Except_orElseLazy___rarg(x_367, x_368);
return x_369;
}
}
else
{
lean_object* x_370; 
lean_dec(x_356);
lean_dec(x_332);
x_370 = lean_box(0);
x_30 = x_370;
goto block_327;
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_array_fget(x_29, x_329);
lean_inc(x_371);
x_372 = l_Lean_Json_getStr_x3f(x_371);
if (lean_obj_tag(x_372) == 0)
{
uint8_t x_373; 
lean_dec(x_371);
lean_dec(x_29);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_375 = l_Except_orElseLazy___rarg(x_372, x_374);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_ctor_get(x_372, 0);
lean_inc(x_376);
lean_dec(x_372);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_376);
x_378 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_379 = l_Except_orElseLazy___rarg(x_377, x_378);
return x_379;
}
}
else
{
uint8_t x_380; 
x_380 = !lean_is_exclusive(x_372);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_ctor_get(x_372, 0);
x_382 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_383 = lean_string_dec_eq(x_381, x_382);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = l_String_toName(x_381);
x_385 = l_Lean_Name_isAnonymous(x_384);
if (x_385 == 0)
{
lean_free_object(x_372);
lean_dec(x_371);
x_30 = x_384;
goto block_327;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_384);
lean_dec(x_29);
x_386 = lean_unsigned_to_nat(80u);
x_387 = l_Lean_Json_pretty(x_371, x_386);
x_388 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_389 = lean_string_append(x_388, x_387);
lean_dec(x_387);
x_390 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_391 = lean_string_append(x_389, x_390);
lean_ctor_set_tag(x_372, 0);
lean_ctor_set(x_372, 0, x_391);
x_392 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_393 = l_Except_orElseLazy___rarg(x_372, x_392);
return x_393;
}
}
else
{
lean_object* x_394; 
lean_free_object(x_372);
lean_dec(x_381);
lean_dec(x_371);
x_394 = lean_box(0);
x_30 = x_394;
goto block_327;
}
}
else
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_395 = lean_ctor_get(x_372, 0);
lean_inc(x_395);
lean_dec(x_372);
x_396 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_397 = lean_string_dec_eq(x_395, x_396);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; 
x_398 = l_String_toName(x_395);
x_399 = l_Lean_Name_isAnonymous(x_398);
if (x_399 == 0)
{
lean_dec(x_371);
x_30 = x_398;
goto block_327;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_398);
lean_dec(x_29);
x_400 = lean_unsigned_to_nat(80u);
x_401 = l_Lean_Json_pretty(x_371, x_400);
x_402 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_403 = lean_string_append(x_402, x_401);
lean_dec(x_401);
x_404 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_405 = lean_string_append(x_403, x_404);
x_406 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_408 = l_Except_orElseLazy___rarg(x_406, x_407);
return x_408;
}
}
else
{
lean_object* x_409; 
lean_dec(x_395);
lean_dec(x_371);
x_409 = lean_box(0);
x_30 = x_409;
goto block_327;
}
}
}
}
block_327:
{
lean_object* x_31; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_array_get_size(x_29);
x_284 = lean_unsigned_to_nat(1u);
x_285 = lean_nat_dec_lt(x_284, x_283);
lean_dec(x_283);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = l_Lean_instInhabitedJson;
x_287 = l_outOfBounds___rarg(x_286);
x_288 = l_Lean_Json_getObj_x3f(x_287);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
lean_dec(x_30);
lean_dec(x_29);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_291 = l_Except_orElseLazy___rarg(x_288, x_290);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_288, 0);
lean_inc(x_292);
lean_dec(x_288);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_295 = l_Except_orElseLazy___rarg(x_293, x_294);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_288, 0);
lean_inc(x_296);
lean_dec(x_288);
x_297 = lean_box(0);
x_298 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_297, x_296);
if (lean_obj_tag(x_298) == 0)
{
uint8_t x_299; 
lean_dec(x_30);
lean_dec(x_29);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_301 = l_Except_orElseLazy___rarg(x_298, x_300);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_298, 0);
lean_inc(x_302);
lean_dec(x_298);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_302);
x_304 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_305 = l_Except_orElseLazy___rarg(x_303, x_304);
return x_305;
}
}
else
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_298, 0);
lean_inc(x_306);
lean_dec(x_298);
x_31 = x_306;
goto block_282;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_array_fget(x_29, x_284);
x_308 = l_Lean_Json_getObj_x3f(x_307);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
lean_dec(x_30);
lean_dec(x_29);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_311 = l_Except_orElseLazy___rarg(x_308, x_310);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_308, 0);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_315 = l_Except_orElseLazy___rarg(x_313, x_314);
return x_315;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_308, 0);
lean_inc(x_316);
lean_dec(x_308);
x_317 = lean_box(0);
x_318 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_317, x_316);
if (lean_obj_tag(x_318) == 0)
{
uint8_t x_319; 
lean_dec(x_30);
lean_dec(x_29);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_321 = l_Except_orElseLazy___rarg(x_318, x_320);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_324 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_325 = l_Except_orElseLazy___rarg(x_323, x_324);
return x_325;
}
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_318, 0);
lean_inc(x_326);
lean_dec(x_318);
x_31 = x_326;
goto block_282;
}
}
}
block_282:
{
lean_object* x_32; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_array_get_size(x_29);
x_277 = lean_unsigned_to_nat(2u);
x_278 = lean_nat_dec_lt(x_277, x_276);
lean_dec(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = l_Lean_instInhabitedJson;
x_280 = l_outOfBounds___rarg(x_279);
x_32 = x_280;
goto block_275;
}
else
{
lean_object* x_281; 
x_281 = lean_array_fget(x_29, x_277);
x_32 = x_281;
goto block_275;
}
block_275:
{
lean_object* x_33; 
x_33 = l_Lean_Json_getBool_x3f(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_36 = l_Except_orElseLazy___rarg(x_33, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_40 = l_Except_orElseLazy___rarg(x_38, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_269 = lean_array_get_size(x_29);
x_270 = lean_unsigned_to_nat(3u);
x_271 = lean_nat_dec_lt(x_270, x_269);
lean_dec(x_269);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = l_Lean_instInhabitedJson;
x_273 = l_outOfBounds___rarg(x_272);
x_42 = x_273;
goto block_268;
}
else
{
lean_object* x_274; 
x_274 = lean_array_fget(x_29, x_270);
x_42 = x_274;
goto block_268;
}
block_268:
{
lean_object* x_43; 
x_43 = l_Lean_Json_getStr_x3f(x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_46 = l_Except_orElseLazy___rarg(x_43, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_50 = l_Except_orElseLazy___rarg(x_48, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_262 = lean_array_get_size(x_29);
x_263 = lean_unsigned_to_nat(4u);
x_264 = lean_nat_dec_lt(x_263, x_262);
lean_dec(x_262);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = l_Lean_instInhabitedJson;
x_266 = l_outOfBounds___rarg(x_265);
x_52 = x_266;
goto block_261;
}
else
{
lean_object* x_267; 
x_267 = lean_array_fget(x_29, x_263);
x_52 = x_267;
goto block_261;
}
block_261:
{
lean_object* x_53; 
x_53 = l_Lean_Json_getStr_x3f(x_52);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_56 = l_Except_orElseLazy___rarg(x_53, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_60 = l_Except_orElseLazy___rarg(x_58, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
 x_62 = lean_box(0);
}
x_197 = lean_array_get_size(x_29);
x_198 = lean_unsigned_to_nat(5u);
x_199 = lean_nat_dec_lt(x_198, x_197);
lean_dec(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Lean_instInhabitedJson;
x_201 = l_outOfBounds___rarg(x_200);
switch (lean_obj_tag(x_201)) {
case 0:
{
lean_object* x_202; 
x_202 = lean_box(0);
x_63 = x_202;
goto block_196;
}
case 1:
{
lean_object* x_203; 
x_203 = l_Lean_Json_getStr_x3f(x_201);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_206 = l_Except_orElseLazy___rarg(x_203, x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_203, 0);
lean_inc(x_207);
lean_dec(x_203);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_210 = l_Except_orElseLazy___rarg(x_208, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_203, 0);
lean_inc(x_211);
lean_dec(x_203);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_63 = x_212;
goto block_196;
}
}
default: 
{
lean_object* x_213; uint8_t x_214; 
lean_inc(x_201);
x_213 = l_Lean_Json_getStr_x3f(x_201);
x_214 = !lean_is_exclusive(x_201);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_201, 0);
lean_dec(x_215);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_216; 
lean_free_object(x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_216 = !lean_is_exclusive(x_213);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_218 = l_Except_orElseLazy___rarg(x_213, x_217);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
lean_dec(x_213);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_222 = l_Except_orElseLazy___rarg(x_220, x_221);
return x_222;
}
}
else
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_213, 0);
lean_inc(x_223);
lean_dec(x_213);
lean_ctor_set_tag(x_201, 1);
lean_ctor_set(x_201, 0, x_223);
x_63 = x_201;
goto block_196;
}
}
else
{
lean_dec(x_201);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_224 = lean_ctor_get(x_213, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_225 = x_213;
} else {
 lean_dec_ref(x_213);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 1, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_224);
x_227 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_228 = l_Except_orElseLazy___rarg(x_226, x_227);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_213, 0);
lean_inc(x_229);
lean_dec(x_213);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_63 = x_230;
goto block_196;
}
}
}
}
}
else
{
lean_object* x_231; 
x_231 = lean_array_fget(x_29, x_198);
switch (lean_obj_tag(x_231)) {
case 0:
{
lean_object* x_232; 
x_232 = lean_box(0);
x_63 = x_232;
goto block_196;
}
case 1:
{
lean_object* x_233; 
x_233 = l_Lean_Json_getStr_x3f(x_231);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_236 = l_Except_orElseLazy___rarg(x_233, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
lean_dec(x_233);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_240 = l_Except_orElseLazy___rarg(x_238, x_239);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_233, 0);
lean_inc(x_241);
lean_dec(x_233);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_63 = x_242;
goto block_196;
}
}
default: 
{
lean_object* x_243; uint8_t x_244; 
lean_inc(x_231);
x_243 = l_Lean_Json_getStr_x3f(x_231);
x_244 = !lean_is_exclusive(x_231);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_231, 0);
lean_dec(x_245);
if (lean_obj_tag(x_243) == 0)
{
uint8_t x_246; 
lean_free_object(x_231);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_246 = !lean_is_exclusive(x_243);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_248 = l_Except_orElseLazy___rarg(x_243, x_247);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_243, 0);
lean_inc(x_249);
lean_dec(x_243);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_251 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_252 = l_Except_orElseLazy___rarg(x_250, x_251);
return x_252;
}
}
else
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_243, 0);
lean_inc(x_253);
lean_dec(x_243);
lean_ctor_set_tag(x_231, 1);
lean_ctor_set(x_231, 0, x_253);
x_63 = x_231;
goto block_196;
}
}
else
{
lean_dec(x_231);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_254 = lean_ctor_get(x_243, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_255 = x_243;
} else {
 lean_dec_ref(x_243);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 1, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_254);
x_257 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_258 = l_Except_orElseLazy___rarg(x_256, x_257);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_243, 0);
lean_inc(x_259);
lean_dec(x_243);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_63 = x_260;
goto block_196;
}
}
}
}
}
block_196:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_array_get_size(x_29);
x_65 = lean_unsigned_to_nat(6u);
x_66 = lean_nat_dec_lt(x_65, x_64);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_29);
x_67 = l_Lean_instInhabitedJson;
x_68 = l_outOfBounds___rarg(x_67);
switch (lean_obj_tag(x_68)) {
case 0:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_70, 0, x_30);
lean_ctor_set(x_70, 1, x_31);
lean_ctor_set(x_70, 2, x_51);
lean_ctor_set(x_70, 3, x_61);
lean_ctor_set(x_70, 4, x_63);
lean_ctor_set(x_70, 5, x_69);
x_71 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_70, sizeof(void*)*6, x_71);
if (lean_is_scalar(x_62)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_62;
}
lean_ctor_set(x_72, 0, x_70);
x_73 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_74 = l_Except_orElseLazy___rarg(x_72, x_73);
return x_74;
}
case 1:
{
lean_object* x_75; 
lean_dec(x_62);
x_75 = l_Lean_Json_getStr_x3f(x_68);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_78 = l_Except_orElseLazy___rarg(x_75, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_82 = l_Except_orElseLazy___rarg(x_80, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_86, 0, x_30);
lean_ctor_set(x_86, 1, x_31);
lean_ctor_set(x_86, 2, x_51);
lean_ctor_set(x_86, 3, x_61);
lean_ctor_set(x_86, 4, x_63);
lean_ctor_set(x_86, 5, x_85);
x_87 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_86, sizeof(void*)*6, x_87);
lean_ctor_set(x_75, 0, x_86);
x_88 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_89 = l_Except_orElseLazy___rarg(x_75, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_75, 0);
lean_inc(x_90);
lean_dec(x_75);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_92, 0, x_30);
lean_ctor_set(x_92, 1, x_31);
lean_ctor_set(x_92, 2, x_51);
lean_ctor_set(x_92, 3, x_61);
lean_ctor_set(x_92, 4, x_63);
lean_ctor_set(x_92, 5, x_91);
x_93 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_93);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_96 = l_Except_orElseLazy___rarg(x_94, x_95);
return x_96;
}
}
}
default: 
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_62);
lean_inc(x_68);
x_97 = l_Lean_Json_getStr_x3f(x_68);
x_98 = !lean_is_exclusive(x_68);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_68, 0);
lean_dec(x_99);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_100; 
lean_free_object(x_68);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
x_100 = !lean_is_exclusive(x_97);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_102 = l_Except_orElseLazy___rarg(x_97, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
lean_dec(x_97);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_106 = l_Except_orElseLazy___rarg(x_104, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_97);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_97, 0);
lean_ctor_set_tag(x_68, 1);
lean_ctor_set(x_68, 0, x_108);
x_109 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_109, 0, x_30);
lean_ctor_set(x_109, 1, x_31);
lean_ctor_set(x_109, 2, x_51);
lean_ctor_set(x_109, 3, x_61);
lean_ctor_set(x_109, 4, x_63);
lean_ctor_set(x_109, 5, x_68);
x_110 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_109, sizeof(void*)*6, x_110);
lean_ctor_set(x_97, 0, x_109);
x_111 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_112 = l_Except_orElseLazy___rarg(x_97, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
lean_dec(x_97);
lean_ctor_set_tag(x_68, 1);
lean_ctor_set(x_68, 0, x_113);
x_114 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_114, 0, x_30);
lean_ctor_set(x_114, 1, x_31);
lean_ctor_set(x_114, 2, x_51);
lean_ctor_set(x_114, 3, x_61);
lean_ctor_set(x_114, 4, x_63);
lean_ctor_set(x_114, 5, x_68);
x_115 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_115);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_117 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_118 = l_Except_orElseLazy___rarg(x_116, x_117);
return x_118;
}
}
}
else
{
lean_dec(x_68);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
x_119 = lean_ctor_get(x_97, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_120 = x_97;
} else {
 lean_dec_ref(x_97);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
x_122 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_123 = l_Except_orElseLazy___rarg(x_121, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_97, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_125 = x_97;
} else {
 lean_dec_ref(x_97);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_124);
x_127 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_127, 0, x_30);
lean_ctor_set(x_127, 1, x_31);
lean_ctor_set(x_127, 2, x_51);
lean_ctor_set(x_127, 3, x_61);
lean_ctor_set(x_127, 4, x_63);
lean_ctor_set(x_127, 5, x_126);
x_128 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_127, sizeof(void*)*6, x_128);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_127);
x_130 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_131 = l_Except_orElseLazy___rarg(x_129, x_130);
return x_131;
}
}
}
}
}
else
{
lean_object* x_132; 
x_132 = lean_array_fget(x_29, x_65);
lean_dec(x_29);
switch (lean_obj_tag(x_132)) {
case 0:
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_134, 0, x_30);
lean_ctor_set(x_134, 1, x_31);
lean_ctor_set(x_134, 2, x_51);
lean_ctor_set(x_134, 3, x_61);
lean_ctor_set(x_134, 4, x_63);
lean_ctor_set(x_134, 5, x_133);
x_135 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_134, sizeof(void*)*6, x_135);
if (lean_is_scalar(x_62)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_62;
}
lean_ctor_set(x_136, 0, x_134);
x_137 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_138 = l_Except_orElseLazy___rarg(x_136, x_137);
return x_138;
}
case 1:
{
lean_object* x_139; 
lean_dec(x_62);
x_139 = l_Lean_Json_getStr_x3f(x_132);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_142 = l_Except_orElseLazy___rarg(x_139, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_139, 0);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_146 = l_Except_orElseLazy___rarg(x_144, x_145);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_139);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_139, 0);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_150, 0, x_30);
lean_ctor_set(x_150, 1, x_31);
lean_ctor_set(x_150, 2, x_51);
lean_ctor_set(x_150, 3, x_61);
lean_ctor_set(x_150, 4, x_63);
lean_ctor_set(x_150, 5, x_149);
x_151 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_150, sizeof(void*)*6, x_151);
lean_ctor_set(x_139, 0, x_150);
x_152 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_153 = l_Except_orElseLazy___rarg(x_139, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
lean_dec(x_139);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_156, 0, x_30);
lean_ctor_set(x_156, 1, x_31);
lean_ctor_set(x_156, 2, x_51);
lean_ctor_set(x_156, 3, x_61);
lean_ctor_set(x_156, 4, x_63);
lean_ctor_set(x_156, 5, x_155);
x_157 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_156, sizeof(void*)*6, x_157);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_156);
x_159 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_160 = l_Except_orElseLazy___rarg(x_158, x_159);
return x_160;
}
}
}
default: 
{
lean_object* x_161; uint8_t x_162; 
lean_dec(x_62);
lean_inc(x_132);
x_161 = l_Lean_Json_getStr_x3f(x_132);
x_162 = !lean_is_exclusive(x_132);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_132, 0);
lean_dec(x_163);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_164; 
lean_free_object(x_132);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_166 = l_Except_orElseLazy___rarg(x_161, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_170 = l_Except_orElseLazy___rarg(x_168, x_169);
return x_170;
}
}
else
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_161);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_161, 0);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 0, x_172);
x_173 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_173, 0, x_30);
lean_ctor_set(x_173, 1, x_31);
lean_ctor_set(x_173, 2, x_51);
lean_ctor_set(x_173, 3, x_61);
lean_ctor_set(x_173, 4, x_63);
lean_ctor_set(x_173, 5, x_132);
x_174 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_173, sizeof(void*)*6, x_174);
lean_ctor_set(x_161, 0, x_173);
x_175 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_176 = l_Except_orElseLazy___rarg(x_161, x_175);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_161, 0);
lean_inc(x_177);
lean_dec(x_161);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 0, x_177);
x_178 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_178, 0, x_30);
lean_ctor_set(x_178, 1, x_31);
lean_ctor_set(x_178, 2, x_51);
lean_ctor_set(x_178, 3, x_61);
lean_ctor_set(x_178, 4, x_63);
lean_ctor_set(x_178, 5, x_132);
x_179 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_178, sizeof(void*)*6, x_179);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_178);
x_181 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_182 = l_Except_orElseLazy___rarg(x_180, x_181);
return x_182;
}
}
}
else
{
lean_dec(x_132);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_51);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_30);
x_183 = lean_ctor_get(x_161, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_184 = x_161;
} else {
 lean_dec_ref(x_161);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
x_186 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_187 = l_Except_orElseLazy___rarg(x_185, x_186);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_188 = lean_ctor_get(x_161, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_189 = x_161;
} else {
 lean_dec_ref(x_161);
 x_189 = lean_box(0);
}
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_188);
x_191 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_191, 0, x_30);
lean_ctor_set(x_191, 1, x_31);
lean_ctor_set(x_191, 2, x_51);
lean_ctor_set(x_191, 3, x_61);
lean_ctor_set(x_191, 4, x_63);
lean_ctor_set(x_191, 5, x_190);
x_192 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_191, sizeof(void*)*6, x_192);
if (lean_is_scalar(x_189)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_189;
}
lean_ctor_set(x_193, 0, x_191);
x_194 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11;
x_195 = l_Except_orElseLazy___rarg(x_193, x_194);
return x_195;
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
}
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("opts", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inherited", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dir", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__9;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__10;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__11;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__12;
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__13;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("path", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__14;
lean_inc(x_1);
x_5 = l_Lean_Json_parseTagged(x_1, x_2, x_3, x_4);
x_6 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2;
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4;
x_8 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6;
x_9 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___boxed), 5, 4);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Except_orElseLazy___rarg(x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Except_orElseLazy___rarg(x_13, x_9);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_109 = lean_array_get_size(x_15);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_nat_dec_lt(x_110, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = l_Lean_instInhabitedJson;
x_113 = l_outOfBounds___rarg(x_112);
lean_inc(x_113);
x_114 = l_Lean_Json_getStr_x3f(x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
lean_dec(x_113);
lean_dec(x_15);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = l_Except_orElseLazy___rarg(x_114, x_9);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Except_orElseLazy___rarg(x_118, x_9);
return x_119;
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_114);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_ctor_get(x_114, 0);
x_122 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_123 = lean_string_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = l_String_toName(x_121);
x_125 = l_Lean_Name_isAnonymous(x_124);
if (x_125 == 0)
{
lean_free_object(x_114);
lean_dec(x_113);
x_16 = x_124;
goto block_108;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_124);
lean_dec(x_15);
x_126 = lean_unsigned_to_nat(80u);
x_127 = l_Lean_Json_pretty(x_113, x_126);
x_128 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_129 = lean_string_append(x_128, x_127);
lean_dec(x_127);
x_130 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_131 = lean_string_append(x_129, x_130);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 0, x_131);
x_132 = l_Except_orElseLazy___rarg(x_114, x_9);
return x_132;
}
}
else
{
lean_object* x_133; 
lean_free_object(x_114);
lean_dec(x_121);
lean_dec(x_113);
x_133 = lean_box(0);
x_16 = x_133;
goto block_108;
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_114, 0);
lean_inc(x_134);
lean_dec(x_114);
x_135 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_136 = lean_string_dec_eq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_String_toName(x_134);
x_138 = l_Lean_Name_isAnonymous(x_137);
if (x_138 == 0)
{
lean_dec(x_113);
x_16 = x_137;
goto block_108;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_137);
lean_dec(x_15);
x_139 = lean_unsigned_to_nat(80u);
x_140 = l_Lean_Json_pretty(x_113, x_139);
x_141 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Except_orElseLazy___rarg(x_145, x_9);
return x_146;
}
}
else
{
lean_object* x_147; 
lean_dec(x_134);
lean_dec(x_113);
x_147 = lean_box(0);
x_16 = x_147;
goto block_108;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_array_fget(x_15, x_110);
lean_inc(x_148);
x_149 = l_Lean_Json_getStr_x3f(x_148);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
lean_dec(x_148);
lean_dec(x_15);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = l_Except_orElseLazy___rarg(x_149, x_9);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = l_Except_orElseLazy___rarg(x_153, x_9);
return x_154;
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_149);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_149, 0);
x_157 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_158 = lean_string_dec_eq(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_String_toName(x_156);
x_160 = l_Lean_Name_isAnonymous(x_159);
if (x_160 == 0)
{
lean_free_object(x_149);
lean_dec(x_148);
x_16 = x_159;
goto block_108;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_159);
lean_dec(x_15);
x_161 = lean_unsigned_to_nat(80u);
x_162 = l_Lean_Json_pretty(x_148, x_161);
x_163 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_166 = lean_string_append(x_164, x_165);
lean_ctor_set_tag(x_149, 0);
lean_ctor_set(x_149, 0, x_166);
x_167 = l_Except_orElseLazy___rarg(x_149, x_9);
return x_167;
}
}
else
{
lean_object* x_168; 
lean_free_object(x_149);
lean_dec(x_156);
lean_dec(x_148);
x_168 = lean_box(0);
x_16 = x_168;
goto block_108;
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_149, 0);
lean_inc(x_169);
lean_dec(x_149);
x_170 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_171 = lean_string_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = l_String_toName(x_169);
x_173 = l_Lean_Name_isAnonymous(x_172);
if (x_173 == 0)
{
lean_dec(x_148);
x_16 = x_172;
goto block_108;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_172);
lean_dec(x_15);
x_174 = lean_unsigned_to_nat(80u);
x_175 = l_Lean_Json_pretty(x_148, x_174);
x_176 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_177 = lean_string_append(x_176, x_175);
lean_dec(x_175);
x_178 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_179 = lean_string_append(x_177, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_Except_orElseLazy___rarg(x_180, x_9);
return x_181;
}
}
else
{
lean_object* x_182; 
lean_dec(x_169);
lean_dec(x_148);
x_182 = lean_box(0);
x_16 = x_182;
goto block_108;
}
}
}
}
block_108:
{
lean_object* x_17; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_array_get_size(x_15);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_dec_lt(x_73, x_72);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Lean_instInhabitedJson;
x_76 = l_outOfBounds___rarg(x_75);
x_77 = l_Lean_Json_getObj_x3f(x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
lean_dec(x_16);
lean_dec(x_15);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = l_Except_orElseLazy___rarg(x_77, x_9);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Except_orElseLazy___rarg(x_81, x_9);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_box(0);
x_85 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_84, x_83);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_dec(x_16);
lean_dec(x_15);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_Except_orElseLazy___rarg(x_85, x_9);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Except_orElseLazy___rarg(x_89, x_9);
return x_90;
}
}
else
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_17 = x_91;
goto block_71;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_array_fget(x_15, x_73);
x_93 = l_Lean_Json_getObj_x3f(x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec(x_16);
lean_dec(x_15);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Except_orElseLazy___rarg(x_93, x_9);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Except_orElseLazy___rarg(x_97, x_9);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_box(0);
x_101 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_100, x_99);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_16);
lean_dec(x_15);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Except_orElseLazy___rarg(x_101, x_9);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Except_orElseLazy___rarg(x_105, x_9);
return x_106;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
lean_dec(x_101);
x_17 = x_107;
goto block_71;
}
}
}
block_71:
{
lean_object* x_18; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_array_get_size(x_15);
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_nat_dec_lt(x_66, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_instInhabitedJson;
x_69 = l_outOfBounds___rarg(x_68);
x_18 = x_69;
goto block_64;
}
else
{
lean_object* x_70; 
x_70 = lean_array_fget(x_15, x_66);
x_18 = x_70;
goto block_64;
}
block_64:
{
lean_object* x_19; 
x_19 = l_Lean_Json_getBool_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Except_orElseLazy___rarg(x_19, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Except_orElseLazy___rarg(x_23, x_9);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_array_get_size(x_15);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_dec_lt(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_29 = l_Lean_instInhabitedJson;
x_30 = l_outOfBounds___rarg(x_29);
x_31 = l_Lean_Json_getStr_x3f(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Except_orElseLazy___rarg(x_31, x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Except_orElseLazy___rarg(x_35, x_9);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_unbox(x_25);
lean_dec(x_25);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
lean_ctor_set(x_31, 0, x_39);
x_41 = l_Except_orElseLazy___rarg(x_31, x_9);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_17);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_unbox(x_25);
lean_dec(x_25);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = l_Except_orElseLazy___rarg(x_45, x_9);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_array_fget(x_15, x_27);
lean_dec(x_15);
x_48 = l_Lean_Json_getStr_x3f(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Except_orElseLazy___rarg(x_48, x_9);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Except_orElseLazy___rarg(x_52, x_9);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_16);
lean_ctor_set(x_56, 1, x_17);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_unbox(x_25);
lean_dec(x_25);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_57);
lean_ctor_set(x_48, 0, x_56);
x_58 = l_Except_orElseLazy___rarg(x_48, x_9);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_16);
lean_ctor_set(x_60, 1, x_17);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_unbox(x_25);
lean_dec(x_25);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_61);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
x_63 = l_Except_orElseLazy___rarg(x_62, x_9);
return x_63;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instFromJsonPackageEntryV6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119_), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1(x_1, x_2, x_4);
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
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2(x_1, x_3);
x_8 = 1;
x_9 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3(x_1, x_2, x_4);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__4(x_1, x_3);
x_8 = 1;
x_9 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
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
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460_(lean_object* x_1) {
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
x_7 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
x_8 = l_Lean_Name_toString(x_2, x_6, x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_4);
x_14 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_mkRelPathString(x_5);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
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
x_23 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2(x_12, x_3);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3;
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
x_30 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15;
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
x_42 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
x_43 = l_Lean_Name_toString(x_34, x_41, x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_48, 0, x_36);
x_49 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_37);
x_52 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_38);
x_55 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__3___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__4(x_47, x_35);
x_59 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3;
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
x_63 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__2;
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
x_73 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
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
x_80 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7;
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
x_90 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
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
x_97 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7;
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
x_107 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonPackageEntryV6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460_), 1, 0);
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
static lean_object* _init_l_Lake_PackageEntry_scope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Manifest_version___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_configFile___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultConfigFile;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_manifestFile_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
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
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15;
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
x_1 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
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
x_4 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
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
x_21 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
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
x_36 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
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
x_46 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
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
x_58 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_54);
x_61 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
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
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
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
x_308 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
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
x_333 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
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
x_339 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_340 = lean_string_append(x_339, x_338);
lean_dec(x_338);
x_341 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
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
x_352 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
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
x_358 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_359 = lean_string_append(x_358, x_357);
lean_dec(x_357);
x_360 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
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
x_27 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
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
x_75 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5;
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
x_125 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15;
x_126 = lean_string_dec_eq(x_73, x_125);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10;
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
x_131 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
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
x_134 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1;
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
x_152 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3;
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
x_217 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7;
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
static lean_object* _init_l_Lake_Manifest_packagesDir_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_packages___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_packages___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Manifest_packages___default___closed__1;
return x_1;
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
x_4 = l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_9 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119_(x_6);
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
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__1;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__3;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__5;
x_2 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__7() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_Manifest_packages___default___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__8() {
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
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__8;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__11() {
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
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__11;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("incompatible manifest version '", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifest version '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is of a higher major version than this Lake's '", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'; you may need to update your 'lean-toolchain'", 47, 47);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; lean_object* x_31; lean_object* x_139; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_2, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_dec_lt(x_145, x_144);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lake_instOrdStdVer;
x_148 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__12;
lean_inc(x_2);
x_149 = l_instDecidableRelLt___rarg(x_147, x_2, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1;
x_151 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_139 = x_152;
goto block_142;
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_151, 0);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
lean_free_object(x_151);
x_155 = lean_box(0);
x_139 = x_155;
goto block_142;
}
else
{
lean_object* x_156; 
lean_inc(x_154);
x_156 = l_Lean_Json_getStr_x3f(x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
lean_free_object(x_151);
lean_dec(x_154);
lean_dec(x_2);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec(x_156);
x_24 = x_157;
goto block_30;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_160 = lean_string_dec_eq(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = l_String_toName(x_158);
x_162 = l_Lean_Name_isAnonymous(x_161);
if (x_162 == 0)
{
lean_dec(x_154);
lean_ctor_set(x_151, 0, x_161);
x_139 = x_151;
goto block_142;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_161);
lean_free_object(x_151);
lean_dec(x_2);
x_163 = lean_unsigned_to_nat(80u);
x_164 = l_Lean_Json_pretty(x_154, x_163);
x_165 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_166 = lean_string_append(x_165, x_164);
lean_dec(x_164);
x_167 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_168 = lean_string_append(x_166, x_167);
x_24 = x_168;
goto block_30;
}
}
else
{
lean_object* x_169; 
lean_dec(x_158);
lean_free_object(x_151);
lean_dec(x_154);
x_169 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13;
x_139 = x_169;
goto block_142;
}
}
}
}
else
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_151, 0);
lean_inc(x_170);
lean_dec(x_151);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_box(0);
x_139 = x_171;
goto block_142;
}
else
{
lean_object* x_172; 
lean_inc(x_170);
x_172 = l_Lean_Json_getStr_x3f(x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_2);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
x_24 = x_173;
goto block_30;
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12;
x_176 = lean_string_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = l_String_toName(x_174);
x_178 = l_Lean_Name_isAnonymous(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_170);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_177);
x_139 = x_179;
goto block_142;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_177);
lean_dec(x_2);
x_180 = lean_unsigned_to_nat(80u);
x_181 = l_Lean_Json_pretty(x_170, x_180);
x_182 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13;
x_183 = lean_string_append(x_182, x_181);
lean_dec(x_181);
x_184 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_185 = lean_string_append(x_183, x_184);
x_24 = x_185;
goto block_30;
}
}
else
{
lean_object* x_186; 
lean_dec(x_174);
lean_dec(x_170);
x_186 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13;
x_139 = x_186;
goto block_142;
}
}
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_187 = l_Lake_StdVer_toString(x_2);
x_188 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__14;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_193 = l_Lake_StdVer_toString(x_2);
x_194 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__15;
x_195 = lean_string_append(x_194, x_193);
lean_dec(x_193);
x_196 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__16;
x_197 = lean_string_append(x_195, x_196);
x_198 = l_Lake_Manifest_toJson___closed__1;
x_199 = lean_string_append(x_197, x_198);
x_200 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_201 = lean_string_append(x_199, x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__2;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lake_Manifest_version___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__4;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Manifest_version___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__6;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lake_Manifest_version___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__47;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lake_Manifest_version___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_138:
{
lean_object* x_32; lean_object* x_119; lean_object* x_123; lean_object* x_124; 
x_123 = l_Lake_Manifest_toJson___closed__5;
x_124 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_box(0);
x_119 = x_125;
goto block_122;
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_124, 0);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
lean_free_object(x_124);
x_128 = lean_box(0);
x_119 = x_128;
goto block_122;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_Json_getStr_x3f(x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
lean_free_object(x_124);
lean_dec(x_31);
lean_dec(x_2);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec(x_129);
x_17 = x_130;
goto block_23;
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
lean_ctor_set(x_124, 0, x_131);
x_119 = x_124;
goto block_122;
}
}
}
else
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_124, 0);
lean_inc(x_132);
lean_dec(x_124);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_box(0);
x_119 = x_133;
goto block_122;
}
else
{
lean_object* x_134; 
x_134 = l_Lean_Json_getStr_x3f(x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
lean_dec(x_31);
lean_dec(x_2);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_17 = x_135;
goto block_23;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_119 = x_137;
goto block_122;
}
}
}
}
block_118:
{
lean_object* x_33; lean_object* x_103; lean_object* x_104; 
x_103 = l_Lake_Manifest_toJson___closed__7;
x_104 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
x_33 = x_105;
goto block_102;
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_104, 0);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_free_object(x_104);
x_108 = lean_box(0);
x_33 = x_108;
goto block_102;
}
else
{
lean_object* x_109; 
x_109 = l_Lean_Json_getStr_x3f(x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_free_object(x_104);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_10 = x_110;
goto block_16;
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
lean_ctor_set(x_104, 0, x_111);
x_33 = x_104;
goto block_102;
}
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_104, 0);
lean_inc(x_112);
lean_dec(x_104);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_box(0);
x_33 = x_113;
goto block_102;
}
else
{
lean_object* x_114; 
x_114 = l_Lean_Json_getStr_x3f(x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_10 = x_115;
goto block_16;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_33 = x_117;
goto block_102;
}
}
}
}
block_102:
{
lean_object* x_34; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lake_instOrdStdVer;
x_47 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__9;
x_48 = l_instDecidableRelLt___rarg(x_46, x_2, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lake_Manifest_toJson___closed__6;
x_50 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lake_Manifest_packages___default___closed__1;
x_52 = l_Lake_Manifest_fromJson_x3f___lambda__1(x_31, x_32, x_33, x_51);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
switch (lean_obj_tag(x_53)) {
case 0:
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lake_Manifest_packages___default___closed__1;
x_55 = l_Lake_Manifest_fromJson_x3f___lambda__1(x_31, x_32, x_33, x_54);
return x_55;
}
case 4:
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_array_size(x_56);
x_58 = 0;
x_59 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__2(x_57, x_58, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_3 = x_60;
goto block_9;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lake_Manifest_fromJson_x3f___lambda__1(x_31, x_32, x_33, x_61);
return x_62;
}
}
default: 
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_63 = lean_unsigned_to_nat(80u);
x_64 = l_Lean_Json_pretty(x_53, x_63);
x_65 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_68 = lean_string_append(x_66, x_67);
x_3 = x_68;
goto block_9;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lake_Manifest_toJson___closed__6;
x_70 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_1, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_34 = x_71;
goto block_45;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 0);
switch (lean_obj_tag(x_73)) {
case 0:
{
lean_object* x_74; 
lean_free_object(x_70);
x_74 = lean_box(0);
x_34 = x_74;
goto block_45;
}
case 4:
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_array_size(x_75);
x_77 = 0;
x_78 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3(x_76, x_77, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_free_object(x_70);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec(x_78);
x_3 = x_79;
goto block_9;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
lean_ctor_set(x_70, 0, x_80);
x_34 = x_70;
goto block_45;
}
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_70);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_81 = lean_unsigned_to_nat(80u);
x_82 = l_Lean_Json_pretty(x_73, x_81);
x_83 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_86 = lean_string_append(x_84, x_85);
x_3 = x_86;
goto block_9;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_70, 0);
lean_inc(x_87);
lean_dec(x_70);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; 
x_88 = lean_box(0);
x_34 = x_88;
goto block_45;
}
case 4:
{
lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_array_size(x_89);
x_91 = 0;
x_92 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3(x_90, x_91, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_3 = x_93;
goto block_9;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_34 = x_95;
goto block_45;
}
}
default: 
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_96 = lean_unsigned_to_nat(80u);
x_97 = l_Lean_Json_pretty(x_87, x_96);
x_98 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14;
x_101 = lean_string_append(x_99, x_100);
x_3 = x_101;
goto block_9;
}
}
}
}
}
block_45:
{
if (lean_obj_tag(x_34) == 0)
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = 0;
x_36 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__7;
x_37 = l_Lake_Manifest_packages___default___closed__1;
x_38 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1(x_36, x_35, x_37);
x_39 = l_Lake_Manifest_fromJson_x3f___lambda__1(x_31, x_32, x_33, x_38);
return x_39;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_array_size(x_40);
x_42 = 0;
x_43 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1(x_41, x_42, x_40);
x_44 = l_Lake_Manifest_fromJson_x3f___lambda__1(x_31, x_32, x_33, x_43);
return x_44;
}
}
}
}
block_122:
{
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = l_Lake_defaultLakeDir;
x_32 = x_120;
goto block_118;
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_32 = x_121;
goto block_118;
}
}
}
block_142:
{
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
x_140 = lean_box(0);
x_31 = x_140;
goto block_138;
}
else
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_31 = x_141;
goto block_138;
}
}
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_2 = l_Lake_Manifest_toJson___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_fromJson_x3f___closed__1;
x_2 = l_Lake_Manifest_version___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_fromJson_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown manifest version format '", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lake_Manifest_toJson___closed__3;
x_9 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_free_object(x_2);
lean_dec(x_7);
x_10 = l_Lake_Manifest_fromJson_x3f___closed__3;
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lake_Manifest_fromJson_x3f___closed__5;
x_17 = lean_int_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_abs(x_14);
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_15, x_19);
lean_dec(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(80u);
x_22 = l_Lean_Json_pretty(x_11, x_21);
x_23 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_26 = lean_string_append(x_24, x_25);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_free_object(x_2);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
x_28 = l_Lake_Manifest_version___closed__2;
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_27);
x_29 = l_Lake_Manifest_fromJson_x3f___lambda__2(x_7, x_12);
lean_dec(x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(80u);
x_31 = l_Lean_Json_pretty(x_11, x_30);
x_32 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_35 = lean_string_append(x_33, x_34);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = l_Lake_Manifest_fromJson_x3f___closed__5;
x_39 = lean_int_dec_lt(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_nat_abs(x_36);
lean_dec(x_36);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_37, x_41);
lean_dec(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_7);
x_43 = lean_unsigned_to_nat(80u);
x_44 = l_Lean_Json_pretty(x_11, x_43);
x_45 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_48 = lean_string_append(x_46, x_47);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
lean_free_object(x_2);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_41);
x_50 = l_Lake_Manifest_version___closed__2;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lake_Manifest_fromJson_x3f___lambda__2(x_7, x_51);
lean_dec(x_7);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_7);
x_53 = lean_unsigned_to_nat(80u);
x_54 = l_Lean_Json_pretty(x_11, x_53);
x_55 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_58 = lean_string_append(x_56, x_57);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_58);
return x_2;
}
}
}
case 3:
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_2);
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = l_Lake_StdVer_parse(x_59);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Lake_Manifest_fromJson_x3f___lambda__2(x_7, x_64);
lean_dec(x_7);
return x_65;
}
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_7);
x_66 = lean_unsigned_to_nat(80u);
x_67 = l_Lean_Json_pretty(x_11, x_66);
x_68 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_71 = lean_string_append(x_69, x_70);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_71);
return x_2;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l_Lake_Manifest_toJson___closed__3;
x_74 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_72, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_72);
x_75 = l_Lake_Manifest_fromJson_x3f___closed__3;
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
switch (lean_obj_tag(x_76)) {
case 2:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = l_Lake_Manifest_fromJson_x3f___closed__5;
x_82 = lean_int_dec_lt(x_78, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_nat_abs(x_78);
lean_dec(x_78);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_79, x_84);
lean_dec(x_79);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_72);
x_86 = lean_unsigned_to_nat(80u);
x_87 = l_Lean_Json_pretty(x_76, x_86);
x_88 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_76);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_83);
lean_ctor_set(x_93, 2, x_84);
x_94 = l_Lake_Manifest_version___closed__2;
if (lean_is_scalar(x_80)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_80;
}
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lake_Manifest_fromJson_x3f___lambda__2(x_72, x_95);
lean_dec(x_72);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_72);
x_97 = lean_unsigned_to_nat(80u);
x_98 = l_Lean_Json_pretty(x_76, x_97);
x_99 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
x_101 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
case 3:
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_76, 0);
lean_inc(x_104);
lean_dec(x_76);
x_105 = l_Lake_StdVer_parse(x_104);
lean_dec(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_72);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
lean_dec(x_105);
x_110 = l_Lake_Manifest_fromJson_x3f___lambda__2(x_72, x_109);
lean_dec(x_72);
return x_110;
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_72);
x_111 = lean_unsigned_to_nat(80u);
x_112 = l_Lean_Json_pretty(x_76, x_111);
x_113 = l_Lake_Manifest_fromJson_x3f___closed__4;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Manifest_fromJson_x3f___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_fromJson_x3f___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
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
x_1 = lean_mk_string_unchecked("manifest is not valid JSON: ", 28, 28);
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
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_saveToFile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Version(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Manifest(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
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
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__1___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__3);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__4 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__4();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__4);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__5);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__6 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__6();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__6);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__7);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__8 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__8();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__8);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__9 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__9();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__9);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__10);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__11);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__12);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__13);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____lambda__3___closed__14);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__1);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__2);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__3);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__4);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__5);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__6);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__7);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__8 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__8();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__8);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__9 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__9();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__9);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__10 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__10();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__10);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__11 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__11();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__11);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__12 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__12();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__12);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__13 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__13();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__13);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__14 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__14();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__14);
l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15 = _init_l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_119____closed__15);
l_Lake_instFromJsonPackageEntryV6___closed__1 = _init_l_Lake_instFromJsonPackageEntryV6___closed__1();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6___closed__1);
l_Lake_instFromJsonPackageEntryV6 = _init_l_Lake_instFromJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6);
l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1 = _init_l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__1___at___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____spec__2___closed__1);
l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__1 = _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__1();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__1);
l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__2 = _init_l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__2();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_460____closed__2);
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
l_Lake_PackageEntry_scope___default = _init_l_Lake_PackageEntry_scope___default();
lean_mark_persistent(l_Lake_PackageEntry_scope___default);
l_Lake_PackageEntry_configFile___default = _init_l_Lake_PackageEntry_configFile___default();
lean_mark_persistent(l_Lake_PackageEntry_configFile___default);
l_Lake_PackageEntry_manifestFile_x3f___default = _init_l_Lake_PackageEntry_manifestFile_x3f___default();
lean_mark_persistent(l_Lake_PackageEntry_manifestFile_x3f___default);
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
l_Lake_Manifest_packagesDir_x3f___default = _init_l_Lake_Manifest_packagesDir_x3f___default();
lean_mark_persistent(l_Lake_Manifest_packagesDir_x3f___default);
l_Lake_Manifest_packages___default___closed__1 = _init_l_Lake_Manifest_packages___default___closed__1();
lean_mark_persistent(l_Lake_Manifest_packages___default___closed__1);
l_Lake_Manifest_packages___default = _init_l_Lake_Manifest_packages___default();
lean_mark_persistent(l_Lake_Manifest_packages___default);
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
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__1 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__1);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__2 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__2);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__3 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__3);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__4 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__4);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__5 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__5);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__6 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__6);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__7 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__7();
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__8 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__8();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__8);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__9 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__9();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__9);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__10);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__11 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__11();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__11);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__12 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__12();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__12);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__13);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__14 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__14();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__14);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__15 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__15();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__15);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__16 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__16();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__16);
l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17 = _init_l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___lambda__2___closed__17);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

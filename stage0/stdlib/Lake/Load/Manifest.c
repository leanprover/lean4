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
static lean_object* l_Lake_instFromJsonPackageEntryV6___closed__0;
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_Manifest_toJson_spec__0(lean_object*);
static lean_object* l_Lake_Manifest_version___closed__2;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__4____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_Manifest_parse___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__5;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instToJson;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_toJson___closed__1;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4(lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_Manifest_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__10____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_Manifest_toJson___closed__6;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__7;
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__8____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0;
static lean_object* l_Lake_Manifest_version___closed__0;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__1;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0___closed__0;
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__14____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__3(lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__12____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__8____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_PackageEntry_toJson___closed__6;
static lean_object* l_Lake_Manifest_getPackages___closed__2;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__0___closed__0____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_Manifest_toJson___closed__3;
static lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__20;
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__0___closed__1____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_PackageEntry_toJson___closed__2;
static lean_object* l_Lake_Manifest_version___closed__1;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_instFromJson___closed__0;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_128_(lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__0;
static lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1___closed__0;
static lean_object* l_Lake_Manifest_toJson___closed__5;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_Manifest_instFromJson;
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__9____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4___closed__0;
static lean_object* l_Lake_PackageEntry_toJson___closed__3;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__3;
static lean_object* l_Lake_Manifest_toJson___closed__0;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__18;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__10;
static lean_object* l_Lake_PackageEntry_toJson___closed__9;
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_Manifest_getPackages___closed__3;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_128_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instFromJson;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_PackageEntry_toJson___closed__5;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__19;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_PackageEntry_toJson___closed__8;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lake_instToJsonPackageEntryV6;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__11____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_;
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__1;
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_128____boxed(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedPackageEntry___closed__0;
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_Manifest_instToJson;
static lean_object* l_Lake_instToJsonPackageEntryV6___closed__0;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__3;
static lean_object* l_Lake_PackageEntry_instToJson___closed__0;
uint8_t l_Lake_StdVer_compare(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__12;
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__9____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_PackageEntry_toJson___closed__7;
static lean_object* l_Lake_instInhabitedPackageEntryV6___closed__0;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__10;
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__7;
lean_object* l_Lake_StdVer_parse(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2___closed__0;
static lean_object* l_Lake_PackageEntry_toJson___closed__4;
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__4;
LEAN_EXPORT lean_object* l_Lake_instFromJsonPackageEntryV6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_fromJson_x3f___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__6;
static lean_object* l_Lake_Manifest_getVersion___closed__9;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__13____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_Manifest_getVersion___closed__5;
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_Manifest_toJson___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__2____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__17;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_;
LEAN_EXPORT lean_object* l_Lake_Manifest_version;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__0;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__15;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Manifest_toJson___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Manifest_getVersion___closed__2;
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__4;
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__16;
static lean_object* l_Lake_PackageEntry_toJson___closed__0;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntryV6;
static lean_object* l_Lake_fromJsonPackageEntryV6___lam__1___closed__6____x40_Lake_Load_Manifest___hyg_128_;
static lean_object* l_Lake_instInhabitedPackageEntrySrc___closed__0;
static lean_object* l_Lake_Manifest_load___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_saveEntries___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_parse(lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__4;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_Manifest_instFromJson___closed__0;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_NameMap_toJson___at___Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2289__spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__21;
static lean_object* l_Lake_Manifest_instToJson___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_Manifest_getVersion___closed__8;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__13;
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_128____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0(lean_object*);
static lean_object* l_Lake_Manifest_getPackages___closed__5;
static lean_object* l_Lake_Manifest_getVersion___closed__1;
static lean_object* _init_l_Lake_Manifest_version___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_version___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_version___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__1;
x_2 = l_Lake_Manifest_version___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_version() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Manifest_version___closed__2;
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0;
x_11 = lean_string_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_12 = l_String_toName(x_3);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
lean_dec(x_3);
x_14 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(x_12, x_18, x_9);
x_1 = x_19;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_21 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1;
x_22 = lean_string_append(x_21, x_3);
lean_dec(x_3);
x_23 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; 
lean_free_object(x_7);
lean_dec(x_3);
x_25 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
x_30 = lean_box(0);
x_31 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(x_30, x_29, x_9);
x_1 = x_31;
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0;
x_35 = lean_string_dec_eq(x_3, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_inc(x_3);
x_36 = l_String_toName(x_3);
x_37 = l_Lean_Name_isAnonymous(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_3);
x_38 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_6);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec_ref(x_38);
x_43 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(x_36, x_42, x_33);
x_1 = x_43;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_4);
x_45 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1;
x_46 = lean_string_append(x_45, x_3);
lean_dec(x_3);
x_47 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_3);
x_50 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_6);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_55 = lean_box(0);
x_56 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(x_55, x_54, x_33);
x_1 = x_56;
x_2 = x_6;
goto _start;
}
}
}
}
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
}
}
static lean_object* _init_l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_box(1);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0___closed__0;
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_1, x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2___closed__0;
return x_2;
}
else
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
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__0___closed__0____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__0___closed__1____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___lam__0___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_128_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_fromJsonPackageEntryV6___lam__0___closed__1____x40_Lake_Load_Manifest___hyg_128_;
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__2____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__4____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev\?", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__6____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir\?", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__8____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__9____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_128_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_10 = lean_unsigned_to_nat(7u);
x_11 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__2____x40_Lake_Load_Manifest___hyg_128_;
x_12 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__4____x40_Lake_Load_Manifest___hyg_128_;
x_13 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__6____x40_Lake_Load_Manifest___hyg_128_;
x_14 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__8____x40_Lake_Load_Manifest___hyg_128_;
x_15 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__9____x40_Lake_Load_Manifest___hyg_128_;
x_16 = lean_array_push(x_15, x_1);
x_17 = lean_array_push(x_16, x_2);
x_18 = lean_array_push(x_17, x_3);
x_19 = lean_array_push(x_18, x_11);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Json_parseTagged(x_4, x_9, x_10, x_23);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Except_orElseLazy___redArg(x_24, x_5);
lean_dec_ref(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Except_orElseLazy___redArg(x_28, x_5);
lean_dec_ref(x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec_ref(x_24);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_32 = lean_array_get(x_6, x_30, x_31);
x_33 = l_Lean_Name_fromJson_x3f(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_30);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Except_orElseLazy___redArg(x_33, x_5);
lean_dec_ref(x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Except_orElseLazy___redArg(x_37, x_5);
lean_dec_ref(x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec_ref(x_33);
x_40 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
x_41 = lean_array_get(x_6, x_30, x_40);
x_42 = l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0(x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Except_orElseLazy___redArg(x_42, x_5);
lean_dec_ref(x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Except_orElseLazy___redArg(x_46, x_5);
lean_dec_ref(x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec_ref(x_42);
x_49 = lean_unsigned_to_nat(2u);
lean_inc(x_6);
x_50 = lean_array_get(x_6, x_30, x_49);
x_51 = l_Lean_Json_getBool_x3f(x_50);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Except_orElseLazy___redArg(x_51, x_5);
lean_dec_ref(x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Except_orElseLazy___redArg(x_55, x_5);
lean_dec_ref(x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec_ref(x_51);
x_58 = lean_unsigned_to_nat(3u);
lean_inc(x_6);
x_59 = lean_array_get(x_6, x_30, x_58);
x_60 = l_Lean_Json_getStr_x3f(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Except_orElseLazy___redArg(x_60, x_5);
lean_dec_ref(x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Except_orElseLazy___redArg(x_64, x_5);
lean_dec_ref(x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec_ref(x_60);
lean_inc(x_6);
x_67 = lean_array_get(x_6, x_30, x_7);
x_68 = l_Lean_Json_getStr_x3f(x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Except_orElseLazy___redArg(x_68, x_5);
lean_dec_ref(x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Except_orElseLazy___redArg(x_72, x_5);
lean_dec_ref(x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec_ref(x_68);
x_75 = lean_unsigned_to_nat(5u);
lean_inc(x_6);
x_76 = lean_array_get(x_6, x_30, x_75);
x_77 = l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2(x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = l_Except_orElseLazy___redArg(x_77, x_5);
lean_dec_ref(x_77);
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
x_82 = l_Except_orElseLazy___redArg(x_81, x_5);
lean_dec_ref(x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec_ref(x_77);
x_84 = lean_unsigned_to_nat(6u);
x_85 = lean_array_get(x_6, x_30, x_84);
lean_dec(x_30);
x_86 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_83);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_39);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = l_Except_orElseLazy___redArg(x_86, x_5);
lean_dec_ref(x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Except_orElseLazy___redArg(x_90, x_5);
lean_dec_ref(x_90);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_94, 0, x_39);
lean_ctor_set(x_94, 1, x_48);
lean_ctor_set(x_94, 2, x_66);
lean_ctor_set(x_94, 3, x_74);
lean_ctor_set(x_94, 4, x_83);
lean_ctor_set(x_94, 5, x_93);
x_95 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_94, sizeof(void*)*6, x_95);
lean_ctor_set(x_86, 0, x_94);
x_96 = l_Except_orElseLazy___redArg(x_86, x_5);
lean_dec_ref(x_86);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_86, 0);
lean_inc(x_97);
lean_dec(x_86);
x_98 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_98, 0, x_39);
lean_ctor_set(x_98, 1, x_48);
lean_ctor_set(x_98, 2, x_66);
lean_ctor_set(x_98, 3, x_74);
lean_ctor_set(x_98, 4, x_83);
lean_ctor_set(x_98, 5, x_97);
x_99 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_98, sizeof(void*)*6, x_99);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_98);
x_101 = l_Except_orElseLazy___redArg(x_100, x_5);
lean_dec_ref(x_100);
return x_101;
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
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("path", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("opts", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inherited", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dir", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__8____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__9____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__10____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lake_fromJsonPackageEntryV6___closed__9____x40_Lake_Load_Manifest___hyg_128_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__11____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lake_fromJsonPackageEntryV6___closed__10____x40_Lake_Load_Manifest___hyg_128_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__12____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lake_fromJsonPackageEntryV6___closed__11____x40_Lake_Load_Manifest___hyg_128_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__13____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__8____x40_Lake_Load_Manifest___hyg_128_;
x_2 = l_Lake_fromJsonPackageEntryV6___closed__12____x40_Lake_Load_Manifest___hyg_128_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonPackageEntryV6___closed__14____x40_Lake_Load_Manifest___hyg_128_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__13____x40_Lake_Load_Manifest___hyg_128_;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_alloc_closure((void*)(l_Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_128____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_5 = lean_unsigned_to_nat(4u);
x_6 = l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_;
x_7 = l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_;
x_8 = l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_128____boxed), 8, 7);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_2);
lean_closure_set(x_9, 5, x_3);
lean_closure_set(x_9, 6, x_5);
x_10 = l_Lake_fromJsonPackageEntryV6___closed__14____x40_Lake_Load_Manifest___hyg_128_;
x_11 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Except_orElseLazy___redArg(x_11, x_9);
lean_dec_ref(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Except_orElseLazy___redArg(x_15, x_9);
lean_dec_ref(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec_ref(x_11);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_3, x_17, x_18);
x_20 = l_Lean_Name_fromJson_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Except_orElseLazy___redArg(x_20, x_9);
lean_dec_ref(x_20);
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
x_25 = l_Except_orElseLazy___redArg(x_24, x_9);
lean_dec_ref(x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec_ref(x_20);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_get(x_3, x_17, x_27);
x_29 = l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_26);
lean_dec(x_17);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Except_orElseLazy___redArg(x_29, x_9);
lean_dec_ref(x_29);
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
x_34 = l_Except_orElseLazy___redArg(x_33, x_9);
lean_dec_ref(x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec_ref(x_29);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_array_get(x_3, x_17, x_36);
x_38 = l_Lean_Json_getBool_x3f(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_26);
lean_dec(x_17);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Except_orElseLazy___redArg(x_38, x_9);
lean_dec_ref(x_38);
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
x_43 = l_Except_orElseLazy___redArg(x_42, x_9);
lean_dec_ref(x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
lean_dec_ref(x_38);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_array_get(x_3, x_17, x_45);
lean_dec(x_17);
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
x_49 = l_Except_orElseLazy___redArg(x_47, x_9);
lean_dec_ref(x_47);
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
x_52 = l_Except_orElseLazy___redArg(x_51, x_9);
lean_dec_ref(x_51);
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
x_57 = l_Except_orElseLazy___redArg(x_47, x_9);
lean_dec_ref(x_47);
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
x_62 = l_Except_orElseLazy___redArg(x_61, x_9);
lean_dec_ref(x_61);
return x_62;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_128____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_128_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_128____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_128_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_instFromJsonPackageEntryV6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonPackageEntryV6___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0_spec__0(x_1, x_5);
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_3, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___Lean_NameMap_toJson___at___Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2289__spec__1_spec__3___redArg(x_9, x_10, x_7);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(1);
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0_spec__0_spec__0(x_2, x_1);
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__3(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__4(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_7 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_13 = l_Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_16 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_16, 0, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_19 = l_Lake_mkRelPathString(x_5);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
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
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
x_30 = l_Lean_Json_mkObj(x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_34 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_1, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 5);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_39 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_40 = 1;
x_41 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_31, x_40);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_45 = l_Lean_NameMap_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__0(x_32);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_48 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_48, 0, x_33);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_34);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_35);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_57 = l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__3(x_36);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_60 = l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__4(x_37);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_49);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_46);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_43);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Json_mkObj(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_38);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_62);
x_73 = l_Lean_Json_mkObj(x_72);
return x_73;
}
}
}
static lean_object* _init_l_Lake_instToJsonPackageEntryV6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonPackageEntryV6___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntryV6___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_Manifest_version___closed__1;
x_2 = 0;
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntryV6___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_version___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntrySrc___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_instInhabitedPackageEntrySrc___closed__0;
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lake_Manifest_version___closed__1;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntry___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scope", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configFile", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifestFile", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__4;
x_2 = l_Lake_PackageEntry_toJson___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_toJson___closed__6;
x_2 = l_Lake_PackageEntry_toJson___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_toJson___closed__9() {
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_9 = 1;
x_10 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lake_PackageEntry_toJson___closed__0;
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lake_PackageEntry_toJson___closed__1;
x_17 = l_Lake_mkRelPathString(x_5);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lake_PackageEntry_toJson___closed__2;
x_21 = l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__4(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_24 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_24, 0, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = l_Lake_PackageEntry_toJson___closed__5;
x_35 = l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_36 = l_Lake_mkRelPathString(x_33);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
x_39 = l_List_appendTR___redArg(x_31, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Json_mkObj(x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
x_43 = l_Lake_PackageEntry_toJson___closed__5;
x_44 = l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_45 = l_Lake_mkRelPathString(x_42);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_26);
x_49 = l_List_appendTR___redArg(x_31, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Json_mkObj(x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_52 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_7, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_7, 3);
lean_inc(x_55);
lean_dec_ref(x_7);
x_56 = l_Lake_PackageEntry_toJson___closed__7;
x_57 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_52);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_53);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lake_PackageEntry_toJson___closed__8;
x_64 = l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__3(x_54);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lake_PackageEntry_toJson___closed__9;
x_67 = l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__4(x_55);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
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
x_73 = l_List_appendTR___redArg(x_31, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Json_mkObj(x_74);
return x_75;
}
}
}
static lean_object* _init_l_Lake_PackageEntry_instToJson___closed__0() {
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
x_1 = l_Lake_PackageEntry_instToJson___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package entry: ", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: name", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package entry '", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown package entry type '", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: url", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: rev", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputRev: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: dir", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dir: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake-manifest.json", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifestFile: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakefile", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: type", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: inherited", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inherited: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configFile: ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_fromJson_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scope: ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; 
x_6 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_8);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_ctor_set_tag(x_6, 0);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_17 = x_6;
} else {
 lean_dec_ref(x_6);
 x_17 = lean_box(0);
}
x_18 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_19 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = l_Lake_PackageEntry_fromJson_x3f___closed__0;
x_2 = x_20;
goto block_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = l_Lean_Name_fromJson_x3f(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_2 = x_26;
goto block_5;
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec_ref(x_23);
x_2 = x_27;
goto block_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_158; lean_object* x_195; lean_object* x_196; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_29 = x_23;
} else {
 lean_dec_ref(x_23);
 x_29 = lean_box(0);
}
x_195 = l_Lake_PackageEntry_toJson___closed__0;
x_196 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_195);
if (lean_obj_tag(x_196) == 0)
{
goto block_194;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2(x_197);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = l_Lake_PackageEntry_fromJson_x3f___closed__21;
x_202 = lean_string_append(x_201, x_200);
lean_dec(x_200);
lean_ctor_set(x_198, 0, x_202);
return x_198;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_198, 0);
lean_inc(x_203);
lean_dec(x_198);
x_204 = l_Lake_PackageEntry_fromJson_x3f___closed__21;
x_205 = lean_string_append(x_204, x_203);
lean_dec(x_203);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
else
{
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_207; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_207 = !lean_is_exclusive(x_198);
if (x_207 == 0)
{
lean_ctor_set_tag(x_198, 0);
return x_198;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_198, 0);
lean_inc(x_208);
lean_dec(x_198);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
else
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_198, 0);
lean_inc(x_210);
lean_dec_ref(x_198);
if (lean_obj_tag(x_210) == 0)
{
goto block_194;
}
else
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_158 = x_211;
goto block_192;
}
}
}
}
block_39:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = l_Lake_PackageEntry_fromJson_x3f___closed__2;
x_32 = 1;
x_33 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_28, x_32);
x_34 = lean_string_append(x_31, x_33);
lean_dec_ref(x_33);
x_35 = l_Lake_PackageEntry_fromJson_x3f___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_30);
lean_dec_ref(x_30);
if (lean_is_scalar(x_29)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_29;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
block_48:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
if (lean_is_scalar(x_22)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_22;
}
lean_ctor_set(x_45, 0, x_40);
x_46 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 4, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_43);
if (lean_is_scalar(x_17)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_17;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
block_58:
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_56);
x_40 = x_50;
x_41 = x_51;
x_42 = x_53;
x_43 = x_54;
x_44 = x_57;
goto block_48;
}
block_76:
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lake_PackageEntry_toJson___closed__9;
x_67 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_66);
lean_dec(x_16);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_29);
x_68 = lean_box(0);
x_49 = x_65;
x_50 = x_59;
x_51 = x_61;
x_52 = x_60;
x_53 = x_62;
x_54 = x_63;
x_55 = x_64;
x_56 = x_68;
goto block_58;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_22);
lean_dec(x_17);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lake_PackageEntry_fromJson_x3f___closed__4;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_30 = x_73;
goto block_39;
}
else
{
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_74; 
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_22);
lean_dec(x_17);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec_ref(x_70);
x_30 = x_74;
goto block_39;
}
else
{
lean_object* x_75; 
lean_dec(x_29);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec_ref(x_70);
x_49 = x_65;
x_50 = x_59;
x_51 = x_61;
x_52 = x_60;
x_53 = x_62;
x_54 = x_63;
x_55 = x_64;
x_56 = x_75;
goto block_58;
}
}
}
}
block_131:
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_83 = lean_string_dec_eq(x_77, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_;
x_85 = lean_string_dec_eq(x_77, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_86 = l_Lake_PackageEntry_fromJson_x3f___closed__5;
x_87 = lean_string_append(x_86, x_77);
lean_dec_ref(x_77);
x_88 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_30 = x_89;
goto block_39;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_77);
x_90 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_91 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_92 = l_Lake_PackageEntry_fromJson_x3f___closed__6;
x_30 = x_92;
goto block_39;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = l_Lean_Json_getStr_x3f(x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Lake_PackageEntry_fromJson_x3f___closed__7;
x_97 = lean_string_append(x_96, x_95);
lean_dec(x_95);
x_30 = x_97;
goto block_39;
}
else
{
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_98; 
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
lean_dec_ref(x_94);
x_30 = x_98;
goto block_39;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
lean_dec_ref(x_94);
x_100 = l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_;
x_101 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_dec(x_99);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_102 = l_Lake_PackageEntry_fromJson_x3f___closed__8;
x_30 = x_102;
goto block_39;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = l_Lean_Json_getStr_x3f(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_99);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lake_PackageEntry_fromJson_x3f___closed__9;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_30 = x_107;
goto block_39;
}
else
{
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_108; 
lean_dec(x_99);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec_ref(x_104);
x_30 = x_108;
goto block_39;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
lean_dec_ref(x_104);
x_110 = l_Lake_PackageEntry_toJson___closed__8;
x_111 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_59 = x_81;
x_60 = x_99;
x_61 = x_78;
x_62 = x_79;
x_63 = x_80;
x_64 = x_109;
x_65 = x_112;
goto block_76;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_109);
lean_dec(x_99);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lake_PackageEntry_fromJson_x3f___closed__10;
x_117 = lean_string_append(x_116, x_115);
lean_dec(x_115);
x_30 = x_117;
goto block_39;
}
else
{
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_118; 
lean_dec(x_109);
lean_dec(x_99);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec_ref(x_114);
x_30 = x_118;
goto block_39;
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
lean_dec_ref(x_114);
x_59 = x_81;
x_60 = x_99;
x_61 = x_78;
x_62 = x_79;
x_63 = x_80;
x_64 = x_109;
x_65 = x_119;
goto block_76;
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
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_77);
x_120 = l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_;
x_121 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_120);
lean_dec(x_16);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
x_122 = l_Lake_PackageEntry_fromJson_x3f___closed__11;
x_30 = x_122;
goto block_39;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = l_Lean_Json_getStr_x3f(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_22);
lean_dec(x_17);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = l_Lake_PackageEntry_fromJson_x3f___closed__12;
x_127 = lean_string_append(x_126, x_125);
lean_dec(x_125);
x_30 = x_127;
goto block_39;
}
else
{
uint8_t x_128; 
lean_dec(x_29);
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
lean_ctor_set_tag(x_124, 0);
x_40 = x_81;
x_41 = x_78;
x_42 = x_79;
x_43 = x_80;
x_44 = x_124;
goto block_48;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_40 = x_81;
x_41 = x_78;
x_42 = x_79;
x_43 = x_80;
x_44 = x_130;
goto block_48;
}
}
}
}
}
block_137:
{
lean_object* x_136; 
x_136 = l_Lake_PackageEntry_fromJson_x3f___closed__13;
x_77 = x_133;
x_78 = x_132;
x_79 = x_134;
x_80 = x_135;
x_81 = x_136;
goto block_131;
}
block_152:
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lake_PackageEntry_toJson___closed__2;
x_143 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_142);
if (lean_obj_tag(x_143) == 0)
{
x_132 = x_138;
x_133 = x_139;
x_134 = x_141;
x_135 = x_140;
goto block_137;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_141);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lake_PackageEntry_fromJson_x3f___closed__14;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_30 = x_148;
goto block_39;
}
else
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_149; 
lean_dec_ref(x_141);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
lean_dec_ref(x_145);
x_30 = x_149;
goto block_39;
}
else
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
lean_dec_ref(x_145);
if (lean_obj_tag(x_150) == 0)
{
x_132 = x_138;
x_133 = x_139;
x_134 = x_141;
x_135 = x_140;
goto block_137;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_77 = x_139;
x_78 = x_138;
x_79 = x_141;
x_80 = x_140;
x_81 = x_151;
goto block_131;
}
}
}
}
}
block_157:
{
lean_object* x_156; 
x_156 = l_Lake_PackageEntry_fromJson_x3f___closed__15;
x_138 = x_154;
x_139 = x_153;
x_140 = x_155;
x_141 = x_156;
goto block_152;
}
block_192:
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Lake_PackageEntry_toJson___closed__3;
x_160 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_161 = l_Lake_PackageEntry_fromJson_x3f___closed__16;
x_30 = x_161;
goto block_39;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = l_Lean_Json_getStr_x3f(x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lake_PackageEntry_fromJson_x3f___closed__17;
x_166 = lean_string_append(x_165, x_164);
lean_dec(x_164);
x_30 = x_166;
goto block_39;
}
else
{
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_167; 
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
lean_dec_ref(x_163);
x_30 = x_167;
goto block_39;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
lean_dec_ref(x_163);
x_169 = l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_;
x_170 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
lean_dec(x_168);
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_171 = l_Lake_PackageEntry_fromJson_x3f___closed__18;
x_30 = x_171;
goto block_39;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = l_Lean_Json_getBool_x3f(x_172);
lean_dec(x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_168);
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = l_Lake_PackageEntry_fromJson_x3f___closed__19;
x_176 = lean_string_append(x_175, x_174);
lean_dec(x_174);
x_30 = x_176;
goto block_39;
}
else
{
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_177; 
lean_dec(x_168);
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec_ref(x_173);
x_30 = x_177;
goto block_39;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
lean_dec_ref(x_173);
x_179 = l_Lake_PackageEntry_toJson___closed__1;
x_180 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_16, x_179);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = lean_unbox(x_178);
lean_dec(x_178);
x_153 = x_168;
x_154 = x_158;
x_155 = x_181;
goto block_157;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec_ref(x_180);
x_183 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_178);
lean_dec(x_168);
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = l_Lake_PackageEntry_fromJson_x3f___closed__20;
x_186 = lean_string_append(x_185, x_184);
lean_dec(x_184);
x_30 = x_186;
goto block_39;
}
else
{
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_187; 
lean_dec(x_178);
lean_dec(x_168);
lean_dec_ref(x_158);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec_ref(x_183);
x_30 = x_187;
goto block_39;
}
else
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
lean_dec_ref(x_183);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = lean_unbox(x_178);
lean_dec(x_178);
x_153 = x_168;
x_154 = x_158;
x_155 = x_189;
goto block_157;
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec_ref(x_188);
x_191 = lean_unbox(x_178);
lean_dec(x_178);
x_138 = x_158;
x_139 = x_168;
x_140 = x_191;
x_141 = x_190;
goto block_152;
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
block_194:
{
lean_object* x_193; 
x_193 = l_Lake_Manifest_version___closed__1;
x_158 = x_193;
goto block_192;
}
}
}
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_2);
lean_dec_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_instFromJson___closed__0() {
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
x_1 = l_Lake_PackageEntry_instFromJson___closed__0;
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
lean_inc_ref(x_3);
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
lean_dec_ref(x_7);
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
lean_dec_ref(x_9);
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
lean_inc_ref(x_17);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_18 = x_3;
} else {
 lean_dec_ref(x_3);
 x_18 = lean_box(0);
}
x_19 = l_Lake_joinRelative(x_1, x_17);
lean_dec_ref(x_17);
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
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_2;
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
x_5 = l_Lake_Manifest_version___closed__1;
x_6 = l_Lake_PackageEntry_fromJson_x3f___closed__15;
x_7 = lean_box(0);
lean_inc_ref(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_4);
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
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
x_16 = l_Lake_Manifest_version___closed__1;
x_17 = l_Lake_PackageEntry_fromJson_x3f___closed__15;
x_18 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
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
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_Manifest_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_Manifest_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_Manifest_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("version", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_version___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_toJson___closed__2;
x_2 = l_Lake_Manifest_toJson___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakeDir", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packagesDir", 11, 11);
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
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_Manifest_toJson___closed__3;
x_7 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_Manifest_toJson___closed__4;
x_13 = l_Lake_mkRelPathString(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lake_Manifest_toJson___closed__5;
x_17 = l_Option_toJson___at___Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_469__spec__4(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_Manifest_toJson___closed__6;
x_20 = l_Array_toJson___at___Lake_Manifest_toJson_spec__0(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Json_mkObj(x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_toJson___at___Lake_Manifest_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Manifest_instToJson___closed__0() {
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
x_1 = l_Lake_Manifest_instToJson___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("incompatible manifest version '", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__1;
x_2 = l_Lake_Manifest_getVersion___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("schema version '", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is of a higher major version than this Lake's '", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'; you may need to update your 'lean-toolchain'", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid version '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("schemaVersion", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: schemaVersion", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_getVersion___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_getVersion___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_29; lean_object* x_38; lean_object* x_69; lean_object* x_70; 
x_69 = l_Lake_Manifest_toJson___closed__0;
x_70 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_1, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lake_Manifest_getVersion___closed__8;
x_72 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = l_Lake_Manifest_getVersion___closed__10;
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec_ref(x_72);
x_38 = x_74;
goto block_68;
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec_ref(x_70);
x_38 = x_75;
goto block_68;
}
block_9:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lake_Manifest_getVersion___closed__0;
x_4 = l_Lake_StdVer_toString(x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_28:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_lt(x_13, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lake_Manifest_getVersion___closed__2;
x_16 = l_Lake_StdVer_compare(x_10, x_15);
if (x_16 == 0)
{
lean_dec_ref(x_11);
x_2 = x_10;
goto block_9;
}
else
{
if (x_14 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
return x_17;
}
else
{
lean_dec_ref(x_11);
x_2 = x_10;
goto block_9;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_11);
x_18 = l_Lake_Manifest_getVersion___closed__3;
x_19 = l_Lake_StdVer_toString(x_10);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = l_Lake_Manifest_getVersion___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lake_Manifest_toJson___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lake_Manifest_getVersion___closed__5;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
block_37:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_Lake_Manifest_getVersion___closed__6;
x_31 = lean_unsigned_to_nat(80u);
x_32 = l_Lean_Json_pretty(x_29, x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec_ref(x_32);
x_34 = l_Lake_Manifest_getVersion___closed__5;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
block_68:
{
switch (lean_obj_tag(x_38)) {
case 2:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lake_Manifest_getVersion___closed__7;
x_45 = lean_int_dec_lt(x_41, x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_46 == 0)
{
lean_free_object(x_39);
lean_dec(x_41);
x_29 = x_38;
goto block_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_38);
x_47 = lean_nat_abs(x_41);
lean_dec(x_41);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_43);
x_49 = l_Lake_Manifest_version___closed__1;
lean_inc_ref(x_48);
lean_ctor_set(x_39, 1, x_49);
lean_ctor_set(x_39, 0, x_48);
x_10 = x_39;
x_11 = x_48;
x_12 = x_43;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_dec(x_42);
lean_dec(x_41);
x_29 = x_38;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lake_Manifest_getVersion___closed__7;
x_54 = lean_int_dec_lt(x_50, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_55 == 0)
{
lean_dec(x_50);
x_29 = x_38;
goto block_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_38);
x_56 = lean_nat_abs(x_50);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_52);
x_58 = l_Lake_Manifest_version___closed__1;
lean_inc_ref(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_10 = x_59;
x_11 = x_57;
x_12 = x_52;
goto block_28;
}
}
else
{
lean_dec(x_51);
lean_dec(x_50);
x_29 = x_38;
goto block_37;
}
}
}
case 3:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_38);
x_61 = l_Lake_StdVer_parse(x_60);
lean_dec_ref(x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec_ref(x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_10 = x_65;
x_11 = x_66;
x_12 = x_67;
goto block_28;
}
}
default: 
{
x_29 = x_38;
goto block_37;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_Lake_PackageEntry_fromJson_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4_spec__4(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4(x_1);
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
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Manifest_getPackages___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_version___closed__1;
x_2 = l_Lake_Manifest_getPackages___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Manifest_getPackages___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packages: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_13; uint8_t x_14; 
x_13 = l_Lake_Manifest_getPackages___closed__4;
x_14 = l_Lake_StdVer_compare(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lake_Manifest_toJson___closed__6;
x_16 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_2, x_15);
if (lean_obj_tag(x_16) == 0)
{
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lake_Manifest_getPackages___closed__5;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lake_Manifest_getPackages___closed__5;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_ctor_set_tag(x_18, 0);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec_ref(x_18);
if (lean_obj_tag(x_30) == 0)
{
goto block_10;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_3 = x_31;
goto block_8;
}
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lake_Manifest_toJson___closed__6;
x_33 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_2, x_32);
if (lean_obj_tag(x_33) == 0)
{
goto block_12;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lake_Manifest_getPackages___closed__5;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lake_Manifest_getPackages___closed__5;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_ctor_set_tag(x_35, 0);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_48) == 0)
{
lean_free_object(x_35);
goto block_12;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_ctor_set(x_35, 0, x_49);
return x_35;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_35, 0);
lean_inc(x_50);
lean_dec(x_35);
if (lean_obj_tag(x_50) == 0)
{
goto block_12;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
}
block_8:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(x_4, x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
block_10:
{
lean_object* x_9; 
x_9 = l_Lake_Manifest_getPackages___closed__0;
x_3 = x_9;
goto block_8;
}
block_12:
{
lean_object* x_11; 
x_11 = l_Lake_Manifest_getPackages___closed__2;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4_spec__4_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_getPackages(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0___closed__0;
return x_2;
}
else
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
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packagesDir: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakeDir: ", 9, 9);
return x_1;
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
lean_dec_ref(x_2);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_28; lean_object* x_29; lean_object* x_48; lean_object* x_51; lean_object* x_72; lean_object* x_73; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_72 = l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_;
x_73 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_72);
if (lean_obj_tag(x_73) == 0)
{
goto block_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0(x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
lean_dec(x_75);
x_81 = l_Lake_PackageEntry_fromJson_x3f___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
else
{
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_84; 
lean_dec(x_11);
lean_dec(x_6);
x_84 = !lean_is_exclusive(x_75);
if (x_84 == 0)
{
lean_ctor_set_tag(x_75, 0);
return x_75;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_75, 0);
lean_inc(x_87);
lean_dec_ref(x_75);
if (lean_obj_tag(x_87) == 0)
{
goto block_71;
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_51 = x_88;
goto block_69;
}
}
}
}
block_27:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lake_Manifest_version___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lake_Manifest_getPackages(x_16, x_6);
lean_dec(x_6);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
block_47:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lake_Manifest_toJson___closed__5;
x_31 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_12 = x_29;
x_13 = x_28;
x_14 = x_32;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lake_Manifest_fromJson_x3f___closed__0;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lake_Manifest_fromJson_x3f___closed__0;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_43; 
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_ctor_set_tag(x_34, 0);
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec_ref(x_34);
x_12 = x_29;
x_13 = x_28;
x_14 = x_46;
goto block_27;
}
}
}
}
block_50:
{
lean_object* x_49; 
x_49 = l_Lake_Manifest_fromJson_x3f___closed__1;
x_28 = x_48;
x_29 = x_49;
goto block_47;
}
block_69:
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lake_Manifest_toJson___closed__4;
x_53 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___redArg(x_6, x_52);
if (lean_obj_tag(x_53) == 0)
{
x_48 = x_51;
goto block_50;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_1472__spec__0_spec__0(x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lake_Manifest_fromJson_x3f___closed__2;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = l_Lake_Manifest_fromJson_x3f___closed__2;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_64; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_55);
if (x_64 == 0)
{
lean_ctor_set_tag(x_55, 0);
return x_55;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
lean_dec(x_55);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
lean_dec_ref(x_55);
if (lean_obj_tag(x_67) == 0)
{
x_48 = x_51;
goto block_50;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_28 = x_51;
x_29 = x_68;
goto block_47;
}
}
}
}
}
block_71:
{
lean_object* x_70; 
x_70 = lean_box(0);
x_51 = x_70;
goto block_69;
}
}
}
}
}
static lean_object* _init_l_Lake_Manifest_instFromJson___closed__0() {
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
x_1 = l_Lake_Manifest_instFromJson___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Manifest_parse___closed__0() {
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
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lake_Manifest_parse___closed__0;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lake_Manifest_parse___closed__0;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = l_Lake_Manifest_fromJson_x3f(x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lake_Manifest_load___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_14 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lake_Manifest_parse___closed__0;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Lake_Manifest_fromJson_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_7 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_Manifest_load___closed__0;
x_9 = lean_string_append(x_1, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec_ref(x_7);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_6;
 lean_ctor_set_tag(x_12, 1);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_14 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lake_Manifest_parse___closed__0;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Lake_Manifest_fromJson_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_7 = x_20;
goto block_13;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_Manifest_load___closed__0;
x_9 = lean_string_append(x_1, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec_ref(x_7);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_6;
 lean_ctor_set_tag(x_12, 1);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 11)
{
uint8_t x_27; 
lean_dec_ref(x_26);
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
return x_3;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
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
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_save(x_1, x_2, x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_7);
x_12 = l_Lake_Manifest_version___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_Manifest_getPackages(x_13, x_6);
lean_dec(x_6);
lean_dec_ref(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lake_Manifest_parse___closed__0;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lake_Manifest_parse___closed__0;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = l_Lake_Manifest_decodeEntries(x_11);
return x_12;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_14 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lake_Manifest_parse___closed__0;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Lake_Manifest_decodeEntries(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_7 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_Manifest_load___closed__0;
x_9 = lean_string_append(x_1, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec_ref(x_7);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_6;
 lean_ctor_set_tag(x_12, 1);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_12; 
x_12 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_22 = l_Lean_Json_parse(x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lake_Manifest_parse___closed__0;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_16 = x_25;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec_ref(x_22);
x_27 = l_Lake_Manifest_decodeEntries(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_free_object(x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_16 = x_28;
goto block_21;
}
else
{
lean_object* x_29; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_ctor_set(x_12, 0, x_29);
return x_12;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lake_Manifest_load___closed__0;
lean_inc_ref(x_1);
x_18 = lean_string_append(x_1, x_17);
x_19 = lean_string_append(x_18, x_16);
lean_dec_ref(x_16);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_3 = x_20;
x_4 = x_15;
goto block_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_38 = l_Lean_Json_parse(x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lake_Manifest_parse___closed__0;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_32 = x_41;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec_ref(x_38);
x_43 = l_Lake_Manifest_decodeEntries(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_32 = x_44;
goto block_37;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_31);
return x_46;
}
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lake_Manifest_load___closed__0;
lean_inc_ref(x_1);
x_34 = lean_string_append(x_1, x_33);
x_35 = lean_string_append(x_34, x_32);
lean_dec_ref(x_32);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_3 = x_36;
x_4 = x_31;
goto block_11;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 11)
{
uint8_t x_48; 
lean_dec_ref(x_47);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_12, 0);
lean_dec(x_49);
x_50 = l_Lake_Manifest_getPackages___closed__1;
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_50);
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_dec(x_12);
x_52 = l_Lake_Manifest_getPackages___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_dec_ref(x_12);
x_3 = x_47;
x_4 = x_54;
goto block_11;
}
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lake_Manifest_load___closed__0;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_io_error_to_string(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Manifest_toJson___closed__2;
x_2 = l_Lake_Manifest_getVersion___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Lake_Manifest_saveEntries___closed__0;
x_5 = l_Lake_Manifest_toJson___closed__6;
x_6 = l_Array_toJson___at___Lake_Manifest_toJson_spec__0(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Json_mkObj(x_10);
x_12 = lean_unsigned_to_nat(80u);
x_13 = l_Lean_Json_pretty(x_11, x_12);
x_14 = 10;
x_15 = lean_string_push(x_13, x_14);
x_16 = l_IO_FS_writeFile(x_1, x_15, x_3);
lean_dec_ref(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_saveEntries(x_1, x_2, x_3);
lean_dec_ref(x_1);
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
l_Lake_Manifest_version___closed__0 = _init_l_Lake_Manifest_version___closed__0();
lean_mark_persistent(l_Lake_Manifest_version___closed__0);
l_Lake_Manifest_version___closed__1 = _init_l_Lake_Manifest_version___closed__1();
lean_mark_persistent(l_Lake_Manifest_version___closed__1);
l_Lake_Manifest_version___closed__2 = _init_l_Lake_Manifest_version___closed__2();
lean_mark_persistent(l_Lake_Manifest_version___closed__2);
l_Lake_Manifest_version = _init_l_Lake_Manifest_version();
lean_mark_persistent(l_Lake_Manifest_version);
l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__0);
l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__1);
l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_foldlM___at___Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0_spec__0___closed__2);
l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0___closed__0 = _init_l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0___closed__0();
lean_mark_persistent(l_Lean_NameMap_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__0___closed__0);
l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_128__spec__2___closed__0);
l_Lake_fromJsonPackageEntryV6___lam__0___closed__0____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__0___closed__0____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__0___closed__0____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__0___closed__1____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__0___closed__1____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__0___closed__1____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__0____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__1____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__2____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__2____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__2____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__3____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__4____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__4____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__4____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__5____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__6____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__6____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__6____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__7____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__8____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__8____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__8____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___lam__1___closed__9____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___lam__1___closed__9____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___lam__1___closed__9____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__0____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__1____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__2____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__3____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__4____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__5____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__6____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__7____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__8____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__8____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__8____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__9____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__9____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__9____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__10____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__10____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__10____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__11____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__11____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__11____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__12____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__12____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__12____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__13____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__13____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__13____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_fromJsonPackageEntryV6___closed__14____x40_Lake_Load_Manifest___hyg_128_ = _init_l_Lake_fromJsonPackageEntryV6___closed__14____x40_Lake_Load_Manifest___hyg_128_();
lean_mark_persistent(l_Lake_fromJsonPackageEntryV6___closed__14____x40_Lake_Load_Manifest___hyg_128_);
l_Lake_instFromJsonPackageEntryV6___closed__0 = _init_l_Lake_instFromJsonPackageEntryV6___closed__0();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6___closed__0);
l_Lake_instFromJsonPackageEntryV6 = _init_l_Lake_instFromJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6);
l_Lake_instToJsonPackageEntryV6___closed__0 = _init_l_Lake_instToJsonPackageEntryV6___closed__0();
lean_mark_persistent(l_Lake_instToJsonPackageEntryV6___closed__0);
l_Lake_instToJsonPackageEntryV6 = _init_l_Lake_instToJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instToJsonPackageEntryV6);
l_Lake_instInhabitedPackageEntryV6___closed__0 = _init_l_Lake_instInhabitedPackageEntryV6___closed__0();
lean_mark_persistent(l_Lake_instInhabitedPackageEntryV6___closed__0);
l_Lake_instInhabitedPackageEntryV6 = _init_l_Lake_instInhabitedPackageEntryV6();
lean_mark_persistent(l_Lake_instInhabitedPackageEntryV6);
l_Lake_instInhabitedPackageEntrySrc___closed__0 = _init_l_Lake_instInhabitedPackageEntrySrc___closed__0();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc___closed__0);
l_Lake_instInhabitedPackageEntrySrc = _init_l_Lake_instInhabitedPackageEntrySrc();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc);
l_Lake_instInhabitedPackageEntry___closed__0 = _init_l_Lake_instInhabitedPackageEntry___closed__0();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry___closed__0);
l_Lake_instInhabitedPackageEntry = _init_l_Lake_instInhabitedPackageEntry();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry);
l_Lake_PackageEntry_toJson___closed__0 = _init_l_Lake_PackageEntry_toJson___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_toJson___closed__0);
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
l_Lake_PackageEntry_instToJson___closed__0 = _init_l_Lake_PackageEntry_instToJson___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_instToJson___closed__0);
l_Lake_PackageEntry_instToJson = _init_l_Lake_PackageEntry_instToJson();
lean_mark_persistent(l_Lake_PackageEntry_instToJson);
l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0 = _init_l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0);
l_Lake_PackageEntry_fromJson_x3f___closed__0 = _init_l_Lake_PackageEntry_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_fromJson_x3f___closed__0);
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
l_Lake_PackageEntry_instFromJson___closed__0 = _init_l_Lake_PackageEntry_instFromJson___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_instFromJson___closed__0);
l_Lake_PackageEntry_instFromJson = _init_l_Lake_PackageEntry_instFromJson();
lean_mark_persistent(l_Lake_PackageEntry_instFromJson);
l_Lake_Manifest_toJson___closed__0 = _init_l_Lake_Manifest_toJson___closed__0();
lean_mark_persistent(l_Lake_Manifest_toJson___closed__0);
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
l_Lake_Manifest_instToJson___closed__0 = _init_l_Lake_Manifest_instToJson___closed__0();
lean_mark_persistent(l_Lake_Manifest_instToJson___closed__0);
l_Lake_Manifest_instToJson = _init_l_Lake_Manifest_instToJson();
lean_mark_persistent(l_Lake_Manifest_instToJson);
l_Lake_Manifest_getVersion___closed__0 = _init_l_Lake_Manifest_getVersion___closed__0();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__0);
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
l_Lake_Manifest_getVersion___closed__8 = _init_l_Lake_Manifest_getVersion___closed__8();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__8);
l_Lake_Manifest_getVersion___closed__9 = _init_l_Lake_Manifest_getVersion___closed__9();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__9);
l_Lake_Manifest_getVersion___closed__10 = _init_l_Lake_Manifest_getVersion___closed__10();
lean_mark_persistent(l_Lake_Manifest_getVersion___closed__10);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1_spec__1___closed__0);
l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__1___closed__0);
l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_Manifest_getPackages_spec__4___closed__0);
l_Lake_Manifest_getPackages___closed__0 = _init_l_Lake_Manifest_getPackages___closed__0();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__0);
l_Lake_Manifest_getPackages___closed__1 = _init_l_Lake_Manifest_getPackages___closed__1();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__1);
l_Lake_Manifest_getPackages___closed__2 = _init_l_Lake_Manifest_getPackages___closed__2();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__2);
l_Lake_Manifest_getPackages___closed__3 = _init_l_Lake_Manifest_getPackages___closed__3();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__3);
l_Lake_Manifest_getPackages___closed__4 = _init_l_Lake_Manifest_getPackages___closed__4();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__4);
l_Lake_Manifest_getPackages___closed__5 = _init_l_Lake_Manifest_getPackages___closed__5();
lean_mark_persistent(l_Lake_Manifest_getPackages___closed__5);
l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_Manifest_fromJson_x3f_spec__0___closed__0);
l_Lake_Manifest_fromJson_x3f___closed__0 = _init_l_Lake_Manifest_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__0);
l_Lake_Manifest_fromJson_x3f___closed__1 = _init_l_Lake_Manifest_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__1);
l_Lake_Manifest_fromJson_x3f___closed__2 = _init_l_Lake_Manifest_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_Manifest_fromJson_x3f___closed__2);
l_Lake_Manifest_instFromJson___closed__0 = _init_l_Lake_Manifest_instFromJson___closed__0();
lean_mark_persistent(l_Lake_Manifest_instFromJson___closed__0);
l_Lake_Manifest_instFromJson = _init_l_Lake_Manifest_instFromJson();
lean_mark_persistent(l_Lake_Manifest_instFromJson);
l_Lake_Manifest_parse___closed__0 = _init_l_Lake_Manifest_parse___closed__0();
lean_mark_persistent(l_Lake_Manifest_parse___closed__0);
l_Lake_Manifest_load___closed__0 = _init_l_Lake_Manifest_load___closed__0();
lean_mark_persistent(l_Lake_Manifest_load___closed__0);
l_Lake_Manifest_saveEntries___closed__0 = _init_l_Lake_Manifest_saveEntries___closed__0();
lean_mark_persistent(l_Lake_Manifest_saveEntries___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

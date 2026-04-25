// Lean compiler output
// Module: Lake.Load.Resolve
// Imports: public import Lake.Config.Workspace public import Lake.Load.Manifest import Lake.Util.IO import Lake.Util.StoreInsts import Lake.Config.Monad import Lake.Load.Materialize import Lake.Load.Lean.Eval import Lake.Load.Package import Init.Data.Range.Polymorphic.Iterators import Init.TacticsExtra import Lean.Runtime
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Env_noToolchainVars(lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_io_exit(uint8_t);
extern lean_object* l_Lake_toolchainFileName;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object*);
uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object*, lean_object*);
uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object*);
uint8_t l_Lake_ToolchainVer_blt(lean_object*, lean_object*);
uint8_t l_Lake_ToolchainVer_ble(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lake_Manifest_save(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__1_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__2_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4_value;
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__6 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__6_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__9_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__10 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__10_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__12;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__13;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "ws.size_packages_pos"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__14 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__15;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__16;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ws"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__17 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__17_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "size_packages_pos"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__18 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__18_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(94, 198, 251, 95, 67, 81, 118, 246)}};
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__19_value_aux_0),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 162, 153, 14, 174, 138, 145)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__19 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__19_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__20;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__21;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__22;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__23;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__24;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__25;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__26;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__27;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__28;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = ": package requires itself (or a package with the same name)"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "could not rename workspace packages directory: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "workspace packages directory changed; renaming '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' to '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3_value;
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = ": no previous manifest, creating one from scratch"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = ": ignoring previous manifest because it failed to load: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": ignoring missing manifest:\n  "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = ": ignoring manifest because it failed to load: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lake_Load_Resolve_0__Lake_restartCode;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\n    from "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (fixed toolchain)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "restarting Lake via Elan"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--install"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "no Elan detected; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "cannot auto-restart; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "updating toolchain to '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "toolchain not updated; multiple toolchain candidates:\n  "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "toolchain not updated; already up-to-date"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "toolchain not updated; no toolchain information found"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "toolchain not updated; multiple toolchain candidates:"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19_value;
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": updating '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' with "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ": running post-update hooks"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "manifest out of date: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " of dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' changed; use `lake update "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "` to update it"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "git revision"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "source kind (git/path)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "git url"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "' not in manifest; use `lake update "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` to add it"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Workspace_materializeDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "missing manifest; use `lake update` to generate one"};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__0 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__0_value;
static const lean_ctor_object l_Lake_Workspace_materializeDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_materializeDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__1 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__1_value;
static const lean_string_object l_Lake_Workspace_materializeDeps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "package-overrides.json"};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__2 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__2_value;
static const lean_string_object l_Lake_Workspace_materializeDeps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 147, .m_capacity = 147, .m_length = 146, .m_data = "manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)"};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__3 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__3_value;
static const lean_ctor_object l_Lake_Workspace_materializeDeps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_materializeDeps___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__4 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object* v_ws_3_, lean_object* v_dep_4_, lean_object* v_lakeOpts_5_, lean_object* v_leanOpts_6_, uint8_t v_reconfigure_7_){
_start:
{
lean_object* v_lakeEnv_8_; lean_object* v_packages_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_manifestEntry_12_; lean_object* v_dir_13_; lean_object* v_pkgDir_14_; lean_object* v_relPkgDir_15_; lean_object* v_remoteUrl_16_; lean_object* v_name_17_; lean_object* v_scope_18_; lean_object* v_configFile_19_; lean_object* v_manifestFile_x3f_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___y_25_; 
v_lakeEnv_8_ = lean_ctor_get(v_ws_3_, 0);
v_packages_9_ = lean_ctor_get(v_ws_3_, 4);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_array_fget_borrowed(v_packages_9_, v___x_10_);
v_manifestEntry_12_ = lean_ctor_get(v_dep_4_, 4);
lean_inc_ref(v_manifestEntry_12_);
v_dir_13_ = lean_ctor_get(v___x_11_, 4);
v_pkgDir_14_ = lean_ctor_get(v_dep_4_, 0);
lean_inc_ref_n(v_pkgDir_14_, 2);
v_relPkgDir_15_ = lean_ctor_get(v_dep_4_, 1);
lean_inc_ref(v_relPkgDir_15_);
v_remoteUrl_16_ = lean_ctor_get(v_dep_4_, 2);
lean_inc_ref(v_remoteUrl_16_);
lean_dec_ref(v_dep_4_);
v_name_17_ = lean_ctor_get(v_manifestEntry_12_, 0);
lean_inc(v_name_17_);
v_scope_18_ = lean_ctor_get(v_manifestEntry_12_, 1);
lean_inc_ref(v_scope_18_);
v_configFile_19_ = lean_ctor_get(v_manifestEntry_12_, 2);
lean_inc_ref_n(v_configFile_19_, 2);
v_manifestFile_x3f_20_ = lean_ctor_get(v_manifestEntry_12_, 3);
lean_inc(v_manifestFile_x3f_20_);
lean_dec_ref(v_manifestEntry_12_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_array_get_size(v_packages_9_);
v___x_23_ = l_Lake_joinRelative(v_pkgDir_14_, v_configFile_19_);
if (lean_obj_tag(v_manifestFile_x3f_20_) == 0)
{
lean_object* v___x_30_; 
v___x_30_ = l_Lake_defaultManifestFile;
v___y_25_ = v___x_30_;
goto v___jp_24_;
}
else
{
lean_object* v_val_31_; 
v_val_31_ = lean_ctor_get(v_manifestFile_x3f_20_, 0);
lean_inc(v_val_31_);
lean_dec_ref(v_manifestFile_x3f_20_);
v___y_25_ = v_val_31_;
goto v___jp_24_;
}
v___jp_24_:
{
lean_object* v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; 
v___x_26_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_27_ = 0;
v___x_28_ = 1;
lean_inc_ref(v_dir_13_);
lean_inc_ref(v_lakeEnv_8_);
v___x_29_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_29_, 0, v_lakeEnv_8_);
lean_ctor_set(v___x_29_, 1, v___x_21_);
lean_ctor_set(v___x_29_, 2, v_dir_13_);
lean_ctor_set(v___x_29_, 3, v___x_22_);
lean_ctor_set(v___x_29_, 4, v_name_17_);
lean_ctor_set(v___x_29_, 5, v_relPkgDir_15_);
lean_ctor_set(v___x_29_, 6, v_pkgDir_14_);
lean_ctor_set(v___x_29_, 7, v_configFile_19_);
lean_ctor_set(v___x_29_, 8, v___x_23_);
lean_ctor_set(v___x_29_, 9, v___x_21_);
lean_ctor_set(v___x_29_, 10, v___y_25_);
lean_ctor_set(v___x_29_, 11, v___x_26_);
lean_ctor_set(v___x_29_, 12, v_lakeOpts_5_);
lean_ctor_set(v___x_29_, 13, v_leanOpts_6_);
lean_ctor_set(v___x_29_, 14, v_scope_18_);
lean_ctor_set(v___x_29_, 15, v_remoteUrl_16_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*16, v_reconfigure_7_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*16 + 1, v___x_27_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*16 + 2, v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object* v_ws_32_, lean_object* v_dep_33_, lean_object* v_lakeOpts_34_, lean_object* v_leanOpts_35_, lean_object* v_reconfigure_36_){
_start:
{
uint8_t v_reconfigure_boxed_37_; lean_object* v_res_38_; 
v_reconfigure_boxed_37_ = lean_unbox(v_reconfigure_36_);
v_res_38_ = l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(v_ws_32_, v_dep_33_, v_lakeOpts_34_, v_leanOpts_35_, v_reconfigure_boxed_37_);
lean_dec_ref(v_ws_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object* v_as_39_, size_t v_i_40_, size_t v_stop_41_, lean_object* v_b_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = lean_usize_dec_eq(v_i_40_, v_stop_41_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v_name_45_; lean_object* v_config_46_; lean_object* v_lakeEnv_47_; lean_object* v_lakeConfig_48_; lean_object* v_lakeCache_49_; lean_object* v_lakeArgs_x3f_50_; lean_object* v_packages_51_; lean_object* v_packageMap_52_; lean_object* v_facetConfigs_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_64_; 
v___x_44_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
v_name_45_ = lean_ctor_get(v___x_44_, 0);
v_config_46_ = lean_ctor_get(v___x_44_, 1);
v_lakeEnv_47_ = lean_ctor_get(v_b_42_, 0);
v_lakeConfig_48_ = lean_ctor_get(v_b_42_, 1);
v_lakeCache_49_ = lean_ctor_get(v_b_42_, 2);
v_lakeArgs_x3f_50_ = lean_ctor_get(v_b_42_, 3);
v_packages_51_ = lean_ctor_get(v_b_42_, 4);
v_packageMap_52_ = lean_ctor_get(v_b_42_, 5);
v_facetConfigs_53_ = lean_ctor_get(v_b_42_, 6);
v_isSharedCheck_64_ = !lean_is_exclusive(v_b_42_);
if (v_isSharedCheck_64_ == 0)
{
v___x_55_ = v_b_42_;
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_facetConfigs_53_);
lean_inc(v_packageMap_52_);
lean_inc(v_packages_51_);
lean_inc(v_lakeArgs_x3f_50_);
lean_inc(v_lakeCache_49_);
lean_inc(v_lakeConfig_48_);
lean_inc(v_lakeEnv_47_);
lean_dec(v_b_42_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
lean_inc(v_config_46_);
lean_inc(v_name_45_);
v___x_57_ = l_Lake_FacetConfigMap_insert(v_name_45_, v_config_46_, v_facetConfigs_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 6, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_lakeEnv_47_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_lakeConfig_48_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_lakeCache_49_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v_lakeArgs_x3f_50_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v_packages_51_);
lean_ctor_set(v_reuseFailAlloc_63_, 5, v_packageMap_52_);
lean_ctor_set(v_reuseFailAlloc_63_, 6, v___x_57_);
v___x_59_ = v_reuseFailAlloc_63_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
size_t v___x_60_; size_t v___x_61_; 
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_40_, v___x_60_);
v_i_40_ = v___x_61_;
v_b_42_ = v___x_59_;
goto _start;
}
}
}
else
{
return v_b_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v_b_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; lean_object* v_res_71_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_as_65_, v_i_boxed_69_, v_stop_boxed_70_, v_b_68_);
lean_dec_ref(v_as_65_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(lean_object* v_decls_72_, lean_object* v_self_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_array_get_size(v_decls_72_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
return v_self_73_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_le(v___x_75_, v___x_75_);
if (v___x_77_ == 0)
{
if (v___x_76_ == 0)
{
return v_self_73_;
}
else
{
size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; 
v___x_78_ = ((size_t)0ULL);
v___x_79_ = lean_usize_of_nat(v___x_75_);
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_72_, v___x_78_, v___x_79_, v_self_73_);
return v___x_80_;
}
}
else
{
size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; 
v___x_81_ = ((size_t)0ULL);
v___x_82_ = lean_usize_of_nat(v___x_75_);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_72_, v___x_81_, v___x_82_, v_self_73_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object* v_decls_84_, lean_object* v_self_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_decls_84_, v_self_85_);
lean_dec_ref(v_decls_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(lean_object* v_k_87_, lean_object* v_v_88_, lean_object* v_t_89_){
_start:
{
if (lean_obj_tag(v_t_89_) == 0)
{
lean_object* v_size_90_; lean_object* v_k_91_; lean_object* v_v_92_; lean_object* v_l_93_; lean_object* v_r_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_374_; 
v_size_90_ = lean_ctor_get(v_t_89_, 0);
v_k_91_ = lean_ctor_get(v_t_89_, 1);
v_v_92_ = lean_ctor_get(v_t_89_, 2);
v_l_93_ = lean_ctor_get(v_t_89_, 3);
v_r_94_ = lean_ctor_get(v_t_89_, 4);
v_isSharedCheck_374_ = !lean_is_exclusive(v_t_89_);
if (v_isSharedCheck_374_ == 0)
{
v___x_96_ = v_t_89_;
v_isShared_97_ = v_isSharedCheck_374_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_r_94_);
lean_inc(v_l_93_);
lean_inc(v_v_92_);
lean_inc(v_k_91_);
lean_inc(v_size_90_);
lean_dec(v_t_89_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_374_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
uint8_t v___x_98_; 
v___x_98_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_87_, v_k_91_);
switch(v___x_98_)
{
case 0:
{
lean_object* v_impl_99_; lean_object* v___x_100_; 
lean_dec(v_size_90_);
v_impl_99_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_87_, v_v_88_, v_l_93_);
v___x_100_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_94_) == 0)
{
lean_object* v_size_101_; lean_object* v_size_102_; lean_object* v_k_103_; lean_object* v_v_104_; lean_object* v_l_105_; lean_object* v_r_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_size_101_ = lean_ctor_get(v_r_94_, 0);
v_size_102_ = lean_ctor_get(v_impl_99_, 0);
lean_inc(v_size_102_);
v_k_103_ = lean_ctor_get(v_impl_99_, 1);
lean_inc(v_k_103_);
v_v_104_ = lean_ctor_get(v_impl_99_, 2);
lean_inc(v_v_104_);
v_l_105_ = lean_ctor_get(v_impl_99_, 3);
lean_inc(v_l_105_);
v_r_106_ = lean_ctor_get(v_impl_99_, 4);
lean_inc(v_r_106_);
v___x_107_ = lean_unsigned_to_nat(3u);
v___x_108_ = lean_nat_mul(v___x_107_, v_size_101_);
v___x_109_ = lean_nat_dec_lt(v___x_108_, v_size_102_);
lean_dec(v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec(v_r_106_);
lean_dec(v_l_105_);
lean_dec(v_v_104_);
lean_dec(v_k_103_);
v___x_110_ = lean_nat_add(v___x_100_, v_size_102_);
lean_dec(v_size_102_);
v___x_111_ = lean_nat_add(v___x_110_, v_size_101_);
lean_dec(v___x_110_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 3, v_impl_99_);
lean_ctor_set(v___x_96_, 0, v___x_111_);
v___x_113_ = v___x_96_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_114_, 3, v_impl_99_);
lean_ctor_set(v_reuseFailAlloc_114_, 4, v_r_94_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_180_; 
v_isSharedCheck_180_ = !lean_is_exclusive(v_impl_99_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; 
v_unused_181_ = lean_ctor_get(v_impl_99_, 4);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_impl_99_, 3);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_impl_99_, 2);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_impl_99_, 1);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_impl_99_, 0);
lean_dec(v_unused_185_);
v___x_116_ = v_impl_99_;
v_isShared_117_ = v_isSharedCheck_180_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_impl_99_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_180_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_size_118_; lean_object* v_size_119_; lean_object* v_k_120_; lean_object* v_v_121_; lean_object* v_l_122_; lean_object* v_r_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_size_118_ = lean_ctor_get(v_l_105_, 0);
v_size_119_ = lean_ctor_get(v_r_106_, 0);
v_k_120_ = lean_ctor_get(v_r_106_, 1);
v_v_121_ = lean_ctor_get(v_r_106_, 2);
v_l_122_ = lean_ctor_get(v_r_106_, 3);
v_r_123_ = lean_ctor_get(v_r_106_, 4);
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = lean_nat_mul(v___x_124_, v_size_118_);
v___x_126_ = lean_nat_dec_lt(v_size_119_, v___x_125_);
lean_dec(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_155_; 
lean_inc(v_r_123_);
lean_inc(v_l_122_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
v_isSharedCheck_155_ = !lean_is_exclusive(v_r_106_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_156_ = lean_ctor_get(v_r_106_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_r_106_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_r_106_, 2);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_106_, 1);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_106_, 0);
lean_dec(v_unused_160_);
v___x_128_ = v_r_106_;
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
else
{
lean_dec(v_r_106_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___x_143_; lean_object* v___y_145_; 
v___x_130_ = lean_nat_add(v___x_100_, v_size_102_);
lean_dec(v_size_102_);
v___x_131_ = lean_nat_add(v___x_130_, v_size_101_);
lean_dec(v___x_130_);
v___x_143_ = lean_nat_add(v___x_100_, v_size_118_);
if (lean_obj_tag(v_l_122_) == 0)
{
lean_object* v_size_153_; 
v_size_153_ = lean_ctor_get(v_l_122_, 0);
lean_inc(v_size_153_);
v___y_145_ = v_size_153_;
goto v___jp_144_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___y_145_ = v___x_154_;
goto v___jp_144_;
}
v___jp_132_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_nat_add(v___y_133_, v___y_135_);
lean_dec(v___y_135_);
lean_dec(v___y_133_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 4, v_r_94_);
lean_ctor_set(v___x_128_, 3, v_r_123_);
lean_ctor_set(v___x_128_, 2, v_v_92_);
lean_ctor_set(v___x_128_, 1, v_k_91_);
lean_ctor_set(v___x_128_, 0, v___x_136_);
v___x_138_ = v___x_128_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_r_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_r_94_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v___x_138_);
lean_ctor_set(v___x_116_, 3, v___y_134_);
lean_ctor_set(v___x_116_, 2, v_v_121_);
lean_ctor_set(v___x_116_, 1, v_k_120_);
lean_ctor_set(v___x_116_, 0, v___x_131_);
v___x_140_ = v___x_116_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___y_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_nat_add(v___x_143_, v___y_145_);
lean_dec(v___y_145_);
lean_dec(v___x_143_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_l_122_);
lean_ctor_set(v___x_96_, 3, v_l_105_);
lean_ctor_set(v___x_96_, 2, v_v_104_);
lean_ctor_set(v___x_96_, 1, v_k_103_);
lean_ctor_set(v___x_96_, 0, v___x_146_);
v___x_148_ = v___x_96_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_k_103_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_v_104_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_l_105_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_l_122_);
v___x_148_ = v_reuseFailAlloc_152_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_nat_add(v___x_100_, v_size_101_);
if (lean_obj_tag(v_r_123_) == 0)
{
lean_object* v_size_150_; 
v_size_150_ = lean_ctor_get(v_r_123_, 0);
lean_inc(v_size_150_);
v___y_133_ = v___x_149_;
v___y_134_ = v___x_148_;
v___y_135_ = v_size_150_;
goto v___jp_132_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___y_133_ = v___x_149_;
v___y_134_ = v___x_148_;
v___y_135_ = v___x_151_;
goto v___jp_132_;
}
}
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_del_object(v___x_96_);
v___x_161_ = lean_nat_add(v___x_100_, v_size_102_);
lean_dec(v_size_102_);
v___x_162_ = lean_nat_add(v___x_161_, v_size_101_);
lean_dec(v___x_161_);
v___x_163_ = lean_nat_add(v___x_100_, v_size_101_);
v___x_164_ = lean_nat_add(v___x_163_, v_size_119_);
lean_dec(v___x_163_);
lean_inc_ref(v_r_94_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v_r_94_);
lean_ctor_set(v___x_116_, 3, v_r_106_);
lean_ctor_set(v___x_116_, 2, v_v_92_);
lean_ctor_set(v___x_116_, 1, v_k_91_);
lean_ctor_set(v___x_116_, 0, v___x_164_);
v___x_166_ = v___x_116_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_r_106_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_r_94_);
v___x_166_ = v_reuseFailAlloc_179_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_isSharedCheck_173_ = !lean_is_exclusive(v_r_94_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; 
v_unused_174_ = lean_ctor_get(v_r_94_, 4);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_r_94_, 3);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_r_94_, 2);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_94_, 1);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_r_94_, 0);
lean_dec(v_unused_178_);
v___x_168_ = v_r_94_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_r_94_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 4, v___x_166_);
lean_ctor_set(v___x_168_, 3, v_l_105_);
lean_ctor_set(v___x_168_, 2, v_v_104_);
lean_ctor_set(v___x_168_, 1, v_k_103_);
lean_ctor_set(v___x_168_, 0, v___x_162_);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_103_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_104_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_105_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v___x_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_186_; 
v_l_186_ = lean_ctor_get(v_impl_99_, 3);
lean_inc(v_l_186_);
if (lean_obj_tag(v_l_186_) == 0)
{
lean_object* v_r_187_; lean_object* v_k_188_; lean_object* v_v_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_200_; 
v_r_187_ = lean_ctor_get(v_impl_99_, 4);
v_k_188_ = lean_ctor_get(v_impl_99_, 1);
v_v_189_ = lean_ctor_get(v_impl_99_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v_impl_99_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; 
v_unused_201_ = lean_ctor_get(v_impl_99_, 3);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_impl_99_, 0);
lean_dec(v_unused_202_);
v___x_191_ = v_impl_99_;
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_r_187_);
lean_inc(v_v_189_);
lean_inc(v_k_188_);
lean_dec(v_impl_99_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 3, v_r_187_);
lean_ctor_set(v___x_191_, 2, v_v_92_);
lean_ctor_set(v___x_191_, 1, v_k_91_);
lean_ctor_set(v___x_191_, 0, v___x_100_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_r_187_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_r_187_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___x_195_);
lean_ctor_set(v___x_96_, 3, v_l_186_);
lean_ctor_set(v___x_96_, 2, v_v_189_);
lean_ctor_set(v___x_96_, 1, v_k_188_);
lean_ctor_set(v___x_96_, 0, v___x_193_);
v___x_197_ = v___x_96_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_r_203_; 
v_r_203_ = lean_ctor_get(v_impl_99_, 4);
lean_inc(v_r_203_);
if (lean_obj_tag(v_r_203_) == 0)
{
lean_object* v_k_204_; lean_object* v_v_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_228_; 
v_k_204_ = lean_ctor_get(v_impl_99_, 1);
v_v_205_ = lean_ctor_get(v_impl_99_, 2);
v_isSharedCheck_228_ = !lean_is_exclusive(v_impl_99_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_229_ = lean_ctor_get(v_impl_99_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_impl_99_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_impl_99_, 0);
lean_dec(v_unused_231_);
v___x_207_ = v_impl_99_;
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_v_205_);
lean_inc(v_k_204_);
lean_dec(v_impl_99_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_k_209_; lean_object* v_v_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_224_; 
v_k_209_ = lean_ctor_get(v_r_203_, 1);
v_v_210_ = lean_ctor_get(v_r_203_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_r_203_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_225_ = lean_ctor_get(v_r_203_, 4);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_r_203_, 3);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_r_203_, 0);
lean_dec(v_unused_227_);
v___x_212_ = v_r_203_;
v_isShared_213_ = v_isSharedCheck_224_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_v_210_);
lean_inc(v_k_209_);
lean_dec(v_r_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_224_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(3u);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 4, v_l_186_);
lean_ctor_set(v___x_212_, 3, v_l_186_);
lean_ctor_set(v___x_212_, 2, v_v_205_);
lean_ctor_set(v___x_212_, 1, v_k_204_);
lean_ctor_set(v___x_212_, 0, v___x_100_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_k_204_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_v_205_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v_l_186_);
v___x_216_ = v_reuseFailAlloc_223_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 4, v_l_186_);
lean_ctor_set(v___x_207_, 2, v_v_92_);
lean_ctor_set(v___x_207_, 1, v_k_91_);
lean_ctor_set(v___x_207_, 0, v___x_100_);
v___x_218_ = v___x_207_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v_l_186_);
v___x_218_ = v_reuseFailAlloc_222_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___x_218_);
lean_ctor_set(v___x_96_, 3, v___x_216_);
lean_ctor_set(v___x_96_, 2, v_v_210_);
lean_ctor_set(v___x_96_, 1, v_k_209_);
lean_ctor_set(v___x_96_, 0, v___x_214_);
v___x_220_ = v___x_96_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_k_209_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_v_210_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(2u);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_r_203_);
lean_ctor_set(v___x_96_, 3, v_impl_99_);
lean_ctor_set(v___x_96_, 0, v___x_232_);
v___x_234_ = v___x_96_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_impl_99_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_r_203_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
case 1:
{
lean_object* v___x_237_; 
lean_dec(v_v_92_);
lean_dec(v_k_91_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 2, v_v_88_);
lean_ctor_set(v___x_96_, 1, v_k_87_);
v___x_237_ = v___x_96_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_size_90_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_r_94_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
default: 
{
lean_object* v_impl_239_; lean_object* v___x_240_; 
lean_dec(v_size_90_);
v_impl_239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_87_, v_v_88_, v_r_94_);
v___x_240_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_93_) == 0)
{
lean_object* v_size_241_; lean_object* v_size_242_; lean_object* v_k_243_; lean_object* v_v_244_; lean_object* v_l_245_; lean_object* v_r_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_size_241_ = lean_ctor_get(v_l_93_, 0);
v_size_242_ = lean_ctor_get(v_impl_239_, 0);
lean_inc(v_size_242_);
v_k_243_ = lean_ctor_get(v_impl_239_, 1);
lean_inc(v_k_243_);
v_v_244_ = lean_ctor_get(v_impl_239_, 2);
lean_inc(v_v_244_);
v_l_245_ = lean_ctor_get(v_impl_239_, 3);
lean_inc(v_l_245_);
v_r_246_ = lean_ctor_get(v_impl_239_, 4);
lean_inc(v_r_246_);
v___x_247_ = lean_unsigned_to_nat(3u);
v___x_248_ = lean_nat_mul(v___x_247_, v_size_241_);
v___x_249_ = lean_nat_dec_lt(v___x_248_, v_size_242_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v_r_246_);
lean_dec(v_l_245_);
lean_dec(v_v_244_);
lean_dec(v_k_243_);
v___x_250_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_251_ = lean_nat_add(v___x_250_, v_size_242_);
lean_dec(v_size_242_);
lean_dec(v___x_250_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_impl_239_);
lean_ctor_set(v___x_96_, 0, v___x_251_);
v___x_253_ = v___x_96_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_impl_239_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
else
{
lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_318_; 
v_isSharedCheck_318_ = !lean_is_exclusive(v_impl_239_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; 
v_unused_319_ = lean_ctor_get(v_impl_239_, 4);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_impl_239_, 3);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_impl_239_, 2);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_impl_239_, 1);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_impl_239_, 0);
lean_dec(v_unused_323_);
v___x_256_ = v_impl_239_;
v_isShared_257_ = v_isSharedCheck_318_;
goto v_resetjp_255_;
}
else
{
lean_dec(v_impl_239_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_318_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_size_258_; lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_l_261_; lean_object* v_r_262_; lean_object* v_size_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_size_258_ = lean_ctor_get(v_l_245_, 0);
v_k_259_ = lean_ctor_get(v_l_245_, 1);
v_v_260_ = lean_ctor_get(v_l_245_, 2);
v_l_261_ = lean_ctor_get(v_l_245_, 3);
v_r_262_ = lean_ctor_get(v_l_245_, 4);
v_size_263_ = lean_ctor_get(v_r_246_, 0);
v___x_264_ = lean_unsigned_to_nat(2u);
v___x_265_ = lean_nat_mul(v___x_264_, v_size_263_);
v___x_266_ = lean_nat_dec_lt(v_size_258_, v___x_265_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_294_; 
lean_inc(v_r_262_);
lean_inc(v_l_261_);
lean_inc(v_v_260_);
lean_inc(v_k_259_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_l_245_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_295_ = lean_ctor_get(v_l_245_, 4);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_245_, 3);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_245_, 2);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_245_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_l_245_, 0);
lean_dec(v_unused_299_);
v___x_268_ = v_l_245_;
v_isShared_269_ = v_isSharedCheck_294_;
goto v_resetjp_267_;
}
else
{
lean_dec(v_l_245_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_294_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_284_; 
v___x_270_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_271_ = lean_nat_add(v___x_270_, v_size_242_);
lean_dec(v_size_242_);
if (lean_obj_tag(v_l_261_) == 0)
{
lean_object* v_size_292_; 
v_size_292_ = lean_ctor_get(v_l_261_, 0);
lean_inc(v_size_292_);
v___y_284_ = v_size_292_;
goto v___jp_283_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___y_284_ = v___x_293_;
goto v___jp_283_;
}
v___jp_272_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_nat_add(v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec(v___y_274_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v_r_246_);
lean_ctor_set(v___x_268_, 3, v_r_262_);
lean_ctor_set(v___x_268_, 2, v_v_244_);
lean_ctor_set(v___x_268_, 1, v_k_243_);
lean_ctor_set(v___x_268_, 0, v___x_276_);
v___x_278_ = v___x_268_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_243_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_244_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_r_262_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_r_246_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v___x_278_);
lean_ctor_set(v___x_256_, 3, v___y_273_);
lean_ctor_set(v___x_256_, 2, v_v_260_);
lean_ctor_set(v___x_256_, 1, v_k_259_);
lean_ctor_set(v___x_256_, 0, v___x_271_);
v___x_280_ = v___x_256_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_v_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v___y_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_nat_add(v___x_270_, v___y_284_);
lean_dec(v___y_284_);
lean_dec(v___x_270_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_l_261_);
lean_ctor_set(v___x_96_, 0, v___x_285_);
v___x_287_ = v___x_96_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_l_261_);
v___x_287_ = v_reuseFailAlloc_291_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_nat_add(v___x_240_, v_size_263_);
if (lean_obj_tag(v_r_262_) == 0)
{
lean_object* v_size_289_; 
v_size_289_ = lean_ctor_get(v_r_262_, 0);
lean_inc(v_size_289_);
v___y_273_ = v___x_287_;
v___y_274_ = v___x_288_;
v___y_275_ = v_size_289_;
goto v___jp_272_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___y_273_ = v___x_287_;
v___y_274_ = v___x_288_;
v___y_275_ = v___x_290_;
goto v___jp_272_;
}
}
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_del_object(v___x_96_);
v___x_300_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_301_ = lean_nat_add(v___x_300_, v_size_242_);
lean_dec(v_size_242_);
v___x_302_ = lean_nat_add(v___x_300_, v_size_258_);
lean_dec(v___x_300_);
lean_inc_ref(v_l_93_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v_l_245_);
lean_ctor_set(v___x_256_, 3, v_l_93_);
lean_ctor_set(v___x_256_, 2, v_v_92_);
lean_ctor_set(v___x_256_, 1, v_k_91_);
lean_ctor_set(v___x_256_, 0, v___x_302_);
v___x_304_ = v___x_256_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_l_245_);
v___x_304_ = v_reuseFailAlloc_317_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v_l_93_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_312_ = lean_ctor_get(v_l_93_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_93_, 3);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_93_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_93_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_93_, 0);
lean_dec(v_unused_316_);
v___x_306_ = v_l_93_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_l_93_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 4, v_r_246_);
lean_ctor_set(v___x_306_, 3, v___x_304_);
lean_ctor_set(v___x_306_, 2, v_v_244_);
lean_ctor_set(v___x_306_, 1, v_k_243_);
lean_ctor_set(v___x_306_, 0, v___x_301_);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_243_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_244_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_r_246_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_324_; 
v_l_324_ = lean_ctor_get(v_impl_239_, 3);
lean_inc(v_l_324_);
if (lean_obj_tag(v_l_324_) == 0)
{
lean_object* v_r_325_; lean_object* v_k_326_; lean_object* v_v_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_350_; 
v_r_325_ = lean_ctor_get(v_impl_239_, 4);
v_k_326_ = lean_ctor_get(v_impl_239_, 1);
v_v_327_ = lean_ctor_get(v_impl_239_, 2);
v_isSharedCheck_350_ = !lean_is_exclusive(v_impl_239_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_351_ = lean_ctor_get(v_impl_239_, 3);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_impl_239_, 0);
lean_dec(v_unused_352_);
v___x_329_ = v_impl_239_;
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_r_325_);
lean_inc(v_v_327_);
lean_inc(v_k_326_);
lean_dec(v_impl_239_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_346_; 
v_k_331_ = lean_ctor_get(v_l_324_, 1);
v_v_332_ = lean_ctor_get(v_l_324_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_l_324_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_347_ = lean_ctor_get(v_l_324_, 4);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_l_324_, 3);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_l_324_, 0);
lean_dec(v_unused_349_);
v___x_334_ = v_l_324_;
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_v_332_);
lean_inc(v_k_331_);
lean_dec(v_l_324_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_325_, 2);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 4, v_r_325_);
lean_ctor_set(v___x_334_, 3, v_r_325_);
lean_ctor_set(v___x_334_, 2, v_v_92_);
lean_ctor_set(v___x_334_, 1, v_k_91_);
lean_ctor_set(v___x_334_, 0, v___x_240_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_r_325_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_r_325_);
v___x_338_ = v_reuseFailAlloc_345_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
lean_inc(v_r_325_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 3, v_r_325_);
lean_ctor_set(v___x_329_, 0, v___x_240_);
v___x_340_ = v___x_329_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_r_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_r_325_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___x_340_);
lean_ctor_set(v___x_96_, 3, v___x_338_);
lean_ctor_set(v___x_96_, 2, v_v_332_);
lean_ctor_set(v___x_96_, 1, v_k_331_);
lean_ctor_set(v___x_96_, 0, v___x_336_);
v___x_342_ = v___x_96_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_331_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_332_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
else
{
lean_object* v_r_353_; 
v_r_353_ = lean_ctor_get(v_impl_239_, 4);
lean_inc(v_r_353_);
if (lean_obj_tag(v_r_353_) == 0)
{
lean_object* v_k_354_; lean_object* v_v_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_366_; 
v_k_354_ = lean_ctor_get(v_impl_239_, 1);
v_v_355_ = lean_ctor_get(v_impl_239_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v_impl_239_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_367_ = lean_ctor_get(v_impl_239_, 4);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_impl_239_, 3);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_impl_239_, 0);
lean_dec(v_unused_369_);
v___x_357_ = v_impl_239_;
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_v_355_);
lean_inc(v_k_354_);
lean_dec(v_impl_239_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_unsigned_to_nat(3u);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v_l_324_);
lean_ctor_set(v___x_357_, 2, v_v_92_);
lean_ctor_set(v___x_357_, 1, v_k_91_);
lean_ctor_set(v___x_357_, 0, v___x_240_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_l_324_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_l_324_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_r_353_);
lean_ctor_set(v___x_96_, 3, v___x_361_);
lean_ctor_set(v___x_96_, 2, v_v_355_);
lean_ctor_set(v___x_96_, 1, v_k_354_);
lean_ctor_set(v___x_96_, 0, v___x_359_);
v___x_363_ = v___x_96_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_k_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_v_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_r_353_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_unsigned_to_nat(2u);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_impl_239_);
lean_ctor_set(v___x_96_, 3, v_r_353_);
lean_ctor_set(v___x_96_, 0, v___x_370_);
v___x_372_ = v___x_96_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_r_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_impl_239_);
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
}
}
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_k_87_);
lean_ctor_set(v___x_376_, 2, v_v_88_);
lean_ctor_set(v___x_376_, 3, v_t_89_);
lean_ctor_set(v___x_376_, 4, v_t_89_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(lean_object* v_ws_377_, lean_object* v_dep_378_, lean_object* v_lakeOpts_379_, lean_object* v_leanOpts_380_, uint8_t v_reconfigure_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_lakeEnv_384_; lean_object* v_lakeConfig_385_; lean_object* v_lakeCache_386_; lean_object* v_lakeArgs_x3f_387_; lean_object* v_packages_388_; lean_object* v_packageMap_389_; lean_object* v_facetConfigs_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_457_; 
v_lakeEnv_384_ = lean_ctor_get(v_ws_377_, 0);
v_lakeConfig_385_ = lean_ctor_get(v_ws_377_, 1);
v_lakeCache_386_ = lean_ctor_get(v_ws_377_, 2);
v_lakeArgs_x3f_387_ = lean_ctor_get(v_ws_377_, 3);
v_packages_388_ = lean_ctor_get(v_ws_377_, 4);
v_packageMap_389_ = lean_ctor_get(v_ws_377_, 5);
v_facetConfigs_390_ = lean_ctor_get(v_ws_377_, 6);
v_isSharedCheck_457_ = !lean_is_exclusive(v_ws_377_);
if (v_isSharedCheck_457_ == 0)
{
v___x_392_ = v_ws_377_;
v_isShared_393_ = v_isSharedCheck_457_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_facetConfigs_390_);
lean_inc(v_packageMap_389_);
lean_inc(v_packages_388_);
lean_inc(v_lakeArgs_x3f_387_);
lean_inc(v_lakeCache_386_);
lean_inc(v_lakeConfig_385_);
lean_inc(v_lakeEnv_384_);
lean_dec(v_ws_377_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_457_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_manifestEntry_396_; lean_object* v_dir_397_; lean_object* v_pkgDir_398_; lean_object* v_relPkgDir_399_; lean_object* v_remoteUrl_400_; lean_object* v_name_401_; lean_object* v_scope_402_; lean_object* v_configFile_403_; lean_object* v_manifestFile_x3f_404_; lean_object* v_wsIdx_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___y_409_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_array_fget_borrowed(v_packages_388_, v___x_394_);
v_manifestEntry_396_ = lean_ctor_get(v_dep_378_, 4);
lean_inc_ref(v_manifestEntry_396_);
v_dir_397_ = lean_ctor_get(v___x_395_, 4);
v_pkgDir_398_ = lean_ctor_get(v_dep_378_, 0);
lean_inc_ref_n(v_pkgDir_398_, 2);
v_relPkgDir_399_ = lean_ctor_get(v_dep_378_, 1);
lean_inc_ref(v_relPkgDir_399_);
v_remoteUrl_400_ = lean_ctor_get(v_dep_378_, 2);
lean_inc_ref(v_remoteUrl_400_);
lean_dec_ref(v_dep_378_);
v_name_401_ = lean_ctor_get(v_manifestEntry_396_, 0);
lean_inc(v_name_401_);
v_scope_402_ = lean_ctor_get(v_manifestEntry_396_, 1);
lean_inc_ref(v_scope_402_);
v_configFile_403_ = lean_ctor_get(v_manifestEntry_396_, 2);
lean_inc_ref_n(v_configFile_403_, 2);
v_manifestFile_x3f_404_ = lean_ctor_get(v_manifestEntry_396_, 3);
lean_inc(v_manifestFile_x3f_404_);
lean_dec_ref(v_manifestEntry_396_);
v_wsIdx_405_ = lean_array_get_size(v_packages_388_);
v___x_406_ = lean_box(0);
v___x_407_ = l_Lake_joinRelative(v_pkgDir_398_, v_configFile_403_);
if (lean_obj_tag(v_manifestFile_x3f_404_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = l_Lake_defaultManifestFile;
v___y_409_ = v___x_455_;
goto v___jp_408_;
}
else
{
lean_object* v_val_456_; 
v_val_456_ = lean_ctor_get(v_manifestFile_x3f_404_, 0);
lean_inc(v_val_456_);
lean_dec_ref(v_manifestFile_x3f_404_);
v___y_409_ = v_val_456_;
goto v___jp_408_;
}
v___jp_408_:
{
lean_object* v___x_410_; uint8_t v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_411_ = 0;
v___x_412_ = 1;
lean_inc(v_name_401_);
lean_inc_ref(v_dir_397_);
lean_inc_ref(v_lakeEnv_384_);
v___x_413_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_413_, 0, v_lakeEnv_384_);
lean_ctor_set(v___x_413_, 1, v___x_406_);
lean_ctor_set(v___x_413_, 2, v_dir_397_);
lean_ctor_set(v___x_413_, 3, v_wsIdx_405_);
lean_ctor_set(v___x_413_, 4, v_name_401_);
lean_ctor_set(v___x_413_, 5, v_relPkgDir_399_);
lean_ctor_set(v___x_413_, 6, v_pkgDir_398_);
lean_ctor_set(v___x_413_, 7, v_configFile_403_);
lean_ctor_set(v___x_413_, 8, v___x_407_);
lean_ctor_set(v___x_413_, 9, v___x_406_);
lean_ctor_set(v___x_413_, 10, v___y_409_);
lean_ctor_set(v___x_413_, 11, v___x_410_);
lean_ctor_set(v___x_413_, 12, v_lakeOpts_379_);
lean_ctor_set(v___x_413_, 13, v_leanOpts_380_);
lean_ctor_set(v___x_413_, 14, v_scope_402_);
lean_ctor_set(v___x_413_, 15, v_remoteUrl_400_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*16, v_reconfigure_381_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*16 + 1, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*16 + 2, v___x_412_);
v___x_414_ = l_Lean_Name_toString(v_name_401_, v___x_411_);
v___x_415_ = l_Lake_resolveConfigFile(v___x_414_, v___x_413_, v_a_382_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_n(v_a_416_, 2);
v_a_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_a_417_);
lean_dec_ref(v___x_415_);
v___x_418_ = l_Lake_loadConfigFile___redArg(v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_436_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_a_420_ = lean_ctor_get(v___x_418_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_436_ == 0)
{
v___x_422_ = v___x_418_;
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_facetDecls_424_; lean_object* v___x_425_; lean_object* v_keyName_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_facetDecls_424_ = lean_ctor_get(v_a_419_, 2);
lean_inc_ref(v_facetDecls_424_);
v___x_425_ = l_Lake_mkPackage(v_a_416_, v_a_419_, v_wsIdx_405_);
lean_dec(v_a_416_);
v_keyName_426_ = lean_ctor_get(v___x_425_, 2);
lean_inc(v_keyName_426_);
lean_inc_ref(v___x_425_);
v___x_427_ = lean_array_push(v_packages_388_, v___x_425_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_426_, v___x_425_, v_packageMap_389_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 5, v___x_428_);
lean_ctor_set(v___x_392_, 4, v___x_427_);
v___x_430_ = v___x_392_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_lakeEnv_384_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_lakeConfig_385_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_lakeCache_386_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_lakeArgs_x3f_387_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_facetConfigs_390_);
v___x_430_ = v_reuseFailAlloc_435_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_facetDecls_424_, v___x_430_);
lean_dec_ref(v_facetDecls_424_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_431_);
v___x_433_ = v___x_422_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_a_420_);
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
else
{
lean_object* v_a_437_; lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_a_416_);
lean_del_object(v___x_392_);
lean_dec(v_facetConfigs_390_);
lean_dec(v_packageMap_389_);
lean_dec_ref(v_packages_388_);
lean_dec(v_lakeArgs_x3f_387_);
lean_dec_ref(v_lakeCache_386_);
lean_dec_ref(v_lakeConfig_385_);
lean_dec_ref(v_lakeEnv_384_);
v_a_437_ = lean_ctor_get(v___x_418_, 0);
v_a_438_ = lean_ctor_get(v___x_418_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_418_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_inc(v_a_437_);
lean_dec(v___x_418_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_del_object(v___x_392_);
lean_dec(v_facetConfigs_390_);
lean_dec(v_packageMap_389_);
lean_dec_ref(v_packages_388_);
lean_dec(v_lakeArgs_x3f_387_);
lean_dec_ref(v_lakeCache_386_);
lean_dec_ref(v_lakeConfig_385_);
lean_dec_ref(v_lakeEnv_384_);
v_a_446_ = lean_ctor_get(v___x_415_, 0);
v_a_447_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_415_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_inc(v_a_446_);
lean_dec(v___x_415_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27___boxed(lean_object* v_ws_458_, lean_object* v_dep_459_, lean_object* v_lakeOpts_460_, lean_object* v_leanOpts_461_, lean_object* v_reconfigure_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
uint8_t v_reconfigure_boxed_465_; lean_object* v_res_466_; 
v_reconfigure_boxed_465_ = lean_unbox(v_reconfigure_462_);
v_res_466_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_458_, v_dep_459_, v_lakeOpts_460_, v_leanOpts_461_, v_reconfigure_boxed_465_, v_a_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_k_468_, lean_object* v_v_469_, lean_object* v_t_470_, lean_object* v_hl_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_468_, v_v_469_, v_t_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(lean_object* v_self_473_, lean_object* v_pkg_474_, lean_object* v_depPkgs_475_){
_start:
{
lean_object* v_wsIdx_476_; lean_object* v_baseName_477_; lean_object* v_keyName_478_; lean_object* v_origName_479_; lean_object* v_dir_480_; lean_object* v_relDir_481_; lean_object* v_config_482_; lean_object* v_configFile_483_; lean_object* v_relConfigFile_484_; lean_object* v_relManifestFile_485_; lean_object* v_scope_486_; lean_object* v_remoteUrl_487_; lean_object* v_depConfigs_488_; lean_object* v_targetDecls_489_; lean_object* v_targetDeclMap_490_; lean_object* v_defaultTargets_491_; lean_object* v_scripts_492_; lean_object* v_defaultScripts_493_; lean_object* v_postUpdateHooks_494_; lean_object* v_buildArchive_495_; lean_object* v_testDriver_496_; lean_object* v_lintDriver_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_520_; 
v_wsIdx_476_ = lean_ctor_get(v_pkg_474_, 0);
v_baseName_477_ = lean_ctor_get(v_pkg_474_, 1);
v_keyName_478_ = lean_ctor_get(v_pkg_474_, 2);
v_origName_479_ = lean_ctor_get(v_pkg_474_, 3);
v_dir_480_ = lean_ctor_get(v_pkg_474_, 4);
v_relDir_481_ = lean_ctor_get(v_pkg_474_, 5);
v_config_482_ = lean_ctor_get(v_pkg_474_, 6);
v_configFile_483_ = lean_ctor_get(v_pkg_474_, 7);
v_relConfigFile_484_ = lean_ctor_get(v_pkg_474_, 8);
v_relManifestFile_485_ = lean_ctor_get(v_pkg_474_, 9);
v_scope_486_ = lean_ctor_get(v_pkg_474_, 10);
v_remoteUrl_487_ = lean_ctor_get(v_pkg_474_, 11);
v_depConfigs_488_ = lean_ctor_get(v_pkg_474_, 12);
v_targetDecls_489_ = lean_ctor_get(v_pkg_474_, 14);
v_targetDeclMap_490_ = lean_ctor_get(v_pkg_474_, 15);
v_defaultTargets_491_ = lean_ctor_get(v_pkg_474_, 16);
v_scripts_492_ = lean_ctor_get(v_pkg_474_, 17);
v_defaultScripts_493_ = lean_ctor_get(v_pkg_474_, 18);
v_postUpdateHooks_494_ = lean_ctor_get(v_pkg_474_, 19);
v_buildArchive_495_ = lean_ctor_get(v_pkg_474_, 20);
v_testDriver_496_ = lean_ctor_get(v_pkg_474_, 21);
v_lintDriver_497_ = lean_ctor_get(v_pkg_474_, 22);
v_isSharedCheck_520_ = !lean_is_exclusive(v_pkg_474_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_pkg_474_, 13);
lean_dec(v_unused_521_);
v___x_499_ = v_pkg_474_;
v_isShared_500_ = v_isSharedCheck_520_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_lintDriver_497_);
lean_inc(v_testDriver_496_);
lean_inc(v_buildArchive_495_);
lean_inc(v_postUpdateHooks_494_);
lean_inc(v_defaultScripts_493_);
lean_inc(v_scripts_492_);
lean_inc(v_defaultTargets_491_);
lean_inc(v_targetDeclMap_490_);
lean_inc(v_targetDecls_489_);
lean_inc(v_depConfigs_488_);
lean_inc(v_remoteUrl_487_);
lean_inc(v_scope_486_);
lean_inc(v_relManifestFile_485_);
lean_inc(v_relConfigFile_484_);
lean_inc(v_configFile_483_);
lean_inc(v_config_482_);
lean_inc(v_relDir_481_);
lean_inc(v_dir_480_);
lean_inc(v_origName_479_);
lean_inc(v_keyName_478_);
lean_inc(v_baseName_477_);
lean_inc(v_wsIdx_476_);
lean_dec(v_pkg_474_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_520_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_lakeEnv_501_; lean_object* v_lakeConfig_502_; lean_object* v_lakeCache_503_; lean_object* v_lakeArgs_x3f_504_; lean_object* v_packages_505_; lean_object* v_packageMap_506_; lean_object* v_facetConfigs_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_lakeEnv_501_ = lean_ctor_get(v_self_473_, 0);
v_lakeConfig_502_ = lean_ctor_get(v_self_473_, 1);
v_lakeCache_503_ = lean_ctor_get(v_self_473_, 2);
v_lakeArgs_x3f_504_ = lean_ctor_get(v_self_473_, 3);
v_packages_505_ = lean_ctor_get(v_self_473_, 4);
v_packageMap_506_ = lean_ctor_get(v_self_473_, 5);
v_facetConfigs_507_ = lean_ctor_get(v_self_473_, 6);
v_isSharedCheck_519_ = !lean_is_exclusive(v_self_473_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_self_473_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_facetConfigs_507_);
lean_inc(v_packageMap_506_);
lean_inc(v_packages_505_);
lean_inc(v_lakeArgs_x3f_504_);
lean_inc(v_lakeCache_503_);
lean_inc(v_lakeConfig_502_);
lean_inc(v_lakeEnv_501_);
lean_dec(v_self_473_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_pkg_512_; 
lean_inc(v_keyName_478_);
lean_inc(v_wsIdx_476_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 13, v_depPkgs_475_);
v_pkg_512_ = v___x_499_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 23, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_wsIdx_476_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_baseName_477_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_keyName_478_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_origName_479_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_dir_480_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v_relDir_481_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_config_482_);
lean_ctor_set(v_reuseFailAlloc_518_, 7, v_configFile_483_);
lean_ctor_set(v_reuseFailAlloc_518_, 8, v_relConfigFile_484_);
lean_ctor_set(v_reuseFailAlloc_518_, 9, v_relManifestFile_485_);
lean_ctor_set(v_reuseFailAlloc_518_, 10, v_scope_486_);
lean_ctor_set(v_reuseFailAlloc_518_, 11, v_remoteUrl_487_);
lean_ctor_set(v_reuseFailAlloc_518_, 12, v_depConfigs_488_);
lean_ctor_set(v_reuseFailAlloc_518_, 13, v_depPkgs_475_);
lean_ctor_set(v_reuseFailAlloc_518_, 14, v_targetDecls_489_);
lean_ctor_set(v_reuseFailAlloc_518_, 15, v_targetDeclMap_490_);
lean_ctor_set(v_reuseFailAlloc_518_, 16, v_defaultTargets_491_);
lean_ctor_set(v_reuseFailAlloc_518_, 17, v_scripts_492_);
lean_ctor_set(v_reuseFailAlloc_518_, 18, v_defaultScripts_493_);
lean_ctor_set(v_reuseFailAlloc_518_, 19, v_postUpdateHooks_494_);
lean_ctor_set(v_reuseFailAlloc_518_, 20, v_buildArchive_495_);
lean_ctor_set(v_reuseFailAlloc_518_, 21, v_testDriver_496_);
lean_ctor_set(v_reuseFailAlloc_518_, 22, v_lintDriver_497_);
v_pkg_512_ = v_reuseFailAlloc_518_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_inc_ref(v_pkg_512_);
v___x_513_ = lean_array_fset(v_packages_505_, v_wsIdx_476_, v_pkg_512_);
lean_dec(v_wsIdx_476_);
v___x_514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_478_, v_pkg_512_, v_packageMap_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 5, v___x_514_);
lean_ctor_set(v___x_509_, 4, v___x_513_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_lakeEnv_501_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_lakeConfig_502_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_lakeCache_503_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_lakeArgs_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_facetConfigs_507_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs(lean_object* v_self_522_, lean_object* v_pkg_523_, lean_object* v_depPkgs_524_, lean_object* v_h_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_self_522_, v_pkg_523_, v_depPkgs_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_527_, lean_object* v_size_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_mk_empty_array_with_capacity(v_size_528_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_ws_527_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_531_, lean_object* v_size_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_531_, v_size_532_);
lean_dec(v_size_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_534_, lean_object* v_wsIdx_535_){
_start:
{
lean_object* v_ws_536_; lean_object* v_depIdxs_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
v_ws_536_ = lean_ctor_get(v_s_534_, 0);
v_depIdxs_537_ = lean_ctor_get(v_s_534_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_s_534_);
if (v_isSharedCheck_545_ == 0)
{
v___x_539_ = v_s_534_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_depIdxs_537_);
lean_inc(v_ws_536_);
lean_dec(v_s_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_array_push(v_depIdxs_537_, v_wsIdx_535_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_ws_536_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_546_, lean_object* v_s_547_, lean_object* v_wsIdx_548_){
_start:
{
lean_object* v_ws_549_; lean_object* v_depIdxs_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_ws_549_ = lean_ctor_get(v_s_547_, 0);
v_depIdxs_550_ = lean_ctor_get(v_s_547_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_s_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v_s_547_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_depIdxs_550_);
lean_inc(v_ws_549_);
lean_dec(v_s_547_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_array_push(v_depIdxs_550_, v_wsIdx_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_ws_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_559_, lean_object* v_s_560_, lean_object* v_wsIdx_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_559_, v_s_560_, v_wsIdx_561_);
lean_dec(v_n_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_563_, lean_object* v_dep_564_, lean_object* v_lakeOpts_565_, lean_object* v_leanOpts_566_, uint8_t v_reconfigure_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_ws_570_; lean_object* v_depIdxs_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_600_; 
v_ws_570_ = lean_ctor_get(v_s_563_, 0);
v_depIdxs_571_ = lean_ctor_get(v_s_563_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_s_563_);
if (v_isSharedCheck_600_ == 0)
{
v___x_573_ = v_s_563_;
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_depIdxs_571_);
lean_inc(v_ws_570_);
lean_dec(v_s_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; 
lean_inc_ref(v_ws_570_);
v___x_575_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_570_, v_dep_564_, v_lakeOpts_565_, v_leanOpts_566_, v_reconfigure_567_, v_a_568_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_590_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_a_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_590_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_packages_581_; lean_object* v_wsIdx_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v_packages_581_ = lean_ctor_get(v_ws_570_, 4);
lean_inc_ref(v_packages_581_);
lean_dec_ref(v_ws_570_);
v_wsIdx_582_ = lean_array_get_size(v_packages_581_);
lean_dec_ref(v_packages_581_);
v___x_583_ = lean_array_push(v_depIdxs_571_, v_wsIdx_582_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_583_);
lean_ctor_set(v___x_573_, 0, v_a_576_);
v___x_585_ = v___x_573_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_585_);
v___x_587_ = v___x_579_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_a_577_);
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
else
{
lean_object* v_a_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_573_);
lean_dec_ref(v_depIdxs_571_);
lean_dec_ref(v_ws_570_);
v_a_591_ = lean_ctor_get(v___x_575_, 0);
v_a_592_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_575_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_inc(v_a_591_);
lean_dec(v___x_575_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_601_, lean_object* v_dep_602_, lean_object* v_lakeOpts_603_, lean_object* v_leanOpts_604_, lean_object* v_reconfigure_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
uint8_t v_reconfigure_boxed_608_; lean_object* v_res_609_; 
v_reconfigure_boxed_608_ = lean_unbox(v_reconfigure_605_);
v_res_609_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_601_, v_dep_602_, v_lakeOpts_603_, v_leanOpts_604_, v_reconfigure_boxed_608_, v_a_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_610_, lean_object* v_s_611_, lean_object* v_dep_612_, lean_object* v_lakeOpts_613_, lean_object* v_leanOpts_614_, uint8_t v_reconfigure_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_ws_618_; lean_object* v_depIdxs_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_648_; 
v_ws_618_ = lean_ctor_get(v_s_611_, 0);
v_depIdxs_619_ = lean_ctor_get(v_s_611_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_648_ == 0)
{
v___x_621_ = v_s_611_;
v_isShared_622_ = v_isSharedCheck_648_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_depIdxs_619_);
lean_inc(v_ws_618_);
lean_dec(v_s_611_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_648_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; 
lean_inc_ref(v_ws_618_);
v___x_623_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_618_, v_dep_612_, v_lakeOpts_613_, v_leanOpts_614_, v_reconfigure_615_, v_a_616_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_638_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_a_625_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_638_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_packages_629_; lean_object* v_wsIdx_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v_packages_629_ = lean_ctor_get(v_ws_618_, 4);
lean_inc_ref(v_packages_629_);
lean_dec_ref(v_ws_618_);
v_wsIdx_630_ = lean_array_get_size(v_packages_629_);
lean_dec_ref(v_packages_629_);
v___x_631_ = lean_array_push(v_depIdxs_619_, v_wsIdx_630_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_631_);
lean_ctor_set(v___x_621_, 0, v_a_624_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_633_);
v___x_635_ = v___x_627_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_a_625_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_621_);
lean_dec_ref(v_depIdxs_619_);
lean_dec_ref(v_ws_618_);
v_a_639_ = lean_ctor_get(v___x_623_, 0);
v_a_640_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_623_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v___x_623_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_649_, lean_object* v_s_650_, lean_object* v_dep_651_, lean_object* v_lakeOpts_652_, lean_object* v_leanOpts_653_, lean_object* v_reconfigure_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
uint8_t v_reconfigure_boxed_657_; lean_object* v_res_658_; 
v_reconfigure_boxed_657_ = lean_unbox(v_reconfigure_654_);
v_res_658_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_649_, v_s_650_, v_dep_651_, v_lakeOpts_652_, v_leanOpts_653_, v_reconfigure_boxed_657_, v_a_655_);
lean_dec(v_n_649_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_apply_2(v_inst_659_, lean_box(0), lean_box(0));
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_661_, lean_object* v_00_u03b1_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_as_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_apply_2(v_inst_663_, lean_box(0), lean_box(0));
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_667_, lean_object* v_00_u03b1_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_as_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_667_, v_00_u03b1_668_, v_inst_669_, v_inst_670_, v_as_671_);
lean_dec_ref(v_as_671_);
lean_dec(v_inst_670_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__12(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__10));
v___x_700_ = l_Lean_mkAtom(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__13(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__12, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__12_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__12);
v___x_702_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5));
v___x_703_ = lean_array_push(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__15(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__14));
v___x_706_ = lean_string_utf8_byte_size(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__16(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__15, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__15_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__15);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__14));
v___x_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
lean_ctor_set(v___x_710_, 2, v___x_707_);
return v___x_710_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__20(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_716_ = lean_box(0);
v___x_717_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__19));
v___x_718_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__16, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__16_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__16);
v___x_719_ = lean_box(2);
v___x_720_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_718_);
lean_ctor_set(v___x_720_, 2, v___x_717_);
lean_ctor_set(v___x_720_, 3, v___x_716_);
return v___x_720_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__21(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__20, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__20_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__20);
v___x_722_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__13, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__13_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__13);
v___x_723_ = lean_array_push(v___x_722_, v___x_721_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__22(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__21, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__21_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__21);
v___x_725_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__11));
v___x_726_ = lean_box(2);
v___x_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_725_);
lean_ctor_set(v___x_727_, 2, v___x_724_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__23(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__22, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__22_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__22);
v___x_729_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5));
v___x_730_ = lean_array_push(v___x_729_, v___x_728_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__24(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__23, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__23_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__23);
v___x_732_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__9));
v___x_733_ = lean_box(2);
v___x_734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
lean_ctor_set(v___x_734_, 2, v___x_731_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__25(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__24, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__24_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__24);
v___x_736_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5));
v___x_737_ = lean_array_push(v___x_736_, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__26(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__25, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__25_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__25);
v___x_739_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__7));
v___x_740_ = lean_box(2);
v___x_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v___x_738_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__27(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__26, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__26_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__26);
v___x_743_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__5));
v___x_744_ = lean_array_push(v___x_743_, v___x_742_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__28(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_745_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__27, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__27_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__27);
v___x_746_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__4));
v___x_747_ = lean_box(2);
v___x_748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
lean_ctor_set(v___x_748_, 2, v___x_745_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1(void){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__28, &l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__28_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1___closed__28);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_toPure_750_, lean_object* v_____do__lift_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_apply_2(v_toPure_750_, lean_box(0), v_____do__lift_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_toPure_753_, lean_object* v_____s_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_2(v_toPure_753_, lean_box(0), v_____s_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_toPure_756_, lean_object* v_____x_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_758_, 0, v_____x_757_);
v___x_759_ = lean_apply_2(v_toPure_756_, lean_box(0), v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_____x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v_packages_762_; lean_object* v___x_763_; 
v_packages_762_ = lean_ctor_get(v_____x_760_, 4);
v___x_763_ = lean_array_fget_borrowed(v_packages_762_, v_x_761_);
lean_inc(v___x_763_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_____x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_____x_764_, v_x_765_);
lean_dec(v_x_765_);
lean_dec_ref(v_____x_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_depIdxs_786_, lean_object* v_pkg_787_, lean_object* v_toPure_788_, lean_object* v_____x_789_){
_start:
{
lean_object* v___f_790_; lean_object* v___x_791_; size_t v_sz_792_; size_t v___x_793_; lean_object* v_depPkgs_794_; lean_object* v_ws_795_; lean_object* v___x_796_; 
lean_inc_ref(v_____x_789_);
v___f_790_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_790_, 0, v_____x_789_);
v___x_791_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9));
v_sz_792_ = lean_array_size(v_depIdxs_786_);
v___x_793_ = ((size_t)0ULL);
v_depPkgs_794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_791_, v___f_790_, v_sz_792_, v___x_793_, v_depIdxs_786_);
v_ws_795_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_____x_789_, v_pkg_787_, v_depPkgs_794_);
v___x_796_ = lean_apply_2(v_toPure_788_, lean_box(0), v_ws_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v_toPure_797_, lean_object* v_next_798_, lean_object* v_G_799_, lean_object* v_____do__lift_800_){
_start:
{
if (lean_obj_tag(v_____do__lift_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
lean_dec(v_G_799_);
v_a_801_ = lean_ctor_get(v_____do__lift_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v_____do__lift_800_);
v___x_802_ = lean_apply_2(v_toPure_797_, lean_box(0), v_a_801_);
return v___x_802_;
}
else
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_toPure_797_);
v_a_803_ = lean_ctor_get(v_____do__lift_800_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v_____do__lift_800_);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_nat_add(v_next_798_, v___x_804_);
v___x_806_ = lean_apply_4(v_G_799_, v___x_805_, v_a_803_, lean_box(0), lean_box(0));
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed(lean_object* v_toPure_807_, lean_object* v_next_808_, lean_object* v_G_809_, lean_object* v_____do__lift_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(v_toPure_807_, v_next_808_, v_G_809_, v_____do__lift_810_);
lean_dec(v_next_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object* v___f_812_, lean_object* v_start_813_, lean_object* v_ws_814_, lean_object* v_toBind_815_, lean_object* v___f_816_, lean_object* v___f_817_, lean_object* v_____x_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_812_, v_start_813_, v_ws_814_, lean_box(0));
lean_inc(v_toBind_815_);
v___x_820_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_819_, v___f_816_);
v___x_821_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_820_, v___f_817_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(lean_object* v___f_822_, lean_object* v_____r_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = lean_apply_1(v___f_822_, v_____r_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object* v_resolve_825_, lean_object* v_pkg_826_, lean_object* v_dep_827_, lean_object* v_ws_828_, lean_object* v_toBind_829_, lean_object* v___f_830_, lean_object* v_____r_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_apply_3(v_resolve_825_, v_pkg_826_, v_dep_827_, v_ws_828_);
v___x_833_ = lean_apply_4(v_toBind_829_, lean_box(0), lean_box(0), v___x_832_, v___f_830_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object* v_start_834_, lean_object* v_s_835_, lean_object* v_opts_836_, lean_object* v_leanOpts_837_, uint8_t v_reconfigure_838_, lean_object* v_inst_839_, lean_object* v_matDep_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_box(v_reconfigure_838_);
v___x_842_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_842_, 0, v_start_834_);
lean_closure_set(v___x_842_, 1, v_s_835_);
lean_closure_set(v___x_842_, 2, v_matDep_840_);
lean_closure_set(v___x_842_, 3, v_opts_836_);
lean_closure_set(v___x_842_, 4, v_leanOpts_837_);
lean_closure_set(v___x_842_, 5, v___x_841_);
v___x_843_ = lean_apply_2(v_inst_839_, lean_box(0), v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object* v_start_844_, lean_object* v_s_845_, lean_object* v_opts_846_, lean_object* v_leanOpts_847_, lean_object* v_reconfigure_848_, lean_object* v_inst_849_, lean_object* v_matDep_850_){
_start:
{
uint8_t v_reconfigure_boxed_851_; lean_object* v_res_852_; 
v_reconfigure_boxed_851_ = lean_unbox(v_reconfigure_848_);
v_res_852_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(v_start_844_, v_s_845_, v_opts_846_, v_leanOpts_847_, v_reconfigure_boxed_851_, v_inst_849_, v_matDep_850_);
return v_res_852_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object* v_dep_853_, lean_object* v_x_854_){
_start:
{
lean_object* v_baseName_855_; lean_object* v_name_856_; uint8_t v___x_857_; 
v_baseName_855_ = lean_ctor_get(v_x_854_, 1);
v_name_856_ = lean_ctor_get(v_dep_853_, 0);
v___x_857_ = lean_name_eq(v_baseName_855_, v_name_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object* v_dep_858_, lean_object* v_x_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(v_dep_858_, v_x_859_);
lean_dec_ref(v_x_859_);
lean_dec_ref(v_dep_858_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object* v_toPure_863_, lean_object* v_start_864_, lean_object* v_leanOpts_865_, uint8_t v_reconfigure_866_, lean_object* v_inst_867_, lean_object* v_resolve_868_, lean_object* v_pkg_869_, lean_object* v_toBind_870_, lean_object* v_baseName_871_, lean_object* v_inst_872_, lean_object* v_dep_873_, lean_object* v_s_874_){
_start:
{
lean_object* v_ws_875_; lean_object* v_depIdxs_876_; lean_object* v_packages_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_ws_875_ = lean_ctor_get(v_s_874_, 0);
lean_inc_ref(v_ws_875_);
v_depIdxs_876_ = lean_ctor_get(v_s_874_, 1);
v_packages_877_ = lean_ctor_get(v_ws_875_, 4);
lean_inc_ref(v_dep_873_);
v___f_878_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_878_, 0, v_dep_873_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_878_, v_packages_877_, v___x_879_);
if (lean_obj_tag(v___x_880_) == 1)
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_890_; 
lean_inc_ref(v_depIdxs_876_);
lean_dec_ref(v_dep_873_);
lean_dec(v_inst_872_);
lean_dec(v_baseName_871_);
lean_dec(v_toBind_870_);
lean_dec_ref(v_pkg_869_);
lean_dec(v_resolve_868_);
lean_dec(v_inst_867_);
lean_dec_ref(v_leanOpts_865_);
lean_dec(v_start_864_);
v_isSharedCheck_890_ = !lean_is_exclusive(v_s_874_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_891_ = lean_ctor_get(v_s_874_, 1);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_s_874_, 0);
lean_dec(v_unused_892_);
v___x_882_ = v_s_874_;
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
else
{
lean_dec(v_s_874_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_val_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v_val_884_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_884_);
lean_dec_ref(v___x_880_);
v___x_885_ = lean_array_push(v_depIdxs_876_, v_val_884_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_ws_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_889_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; 
v___x_888_ = lean_apply_2(v_toPure_863_, lean_box(0), v___x_887_);
return v___x_888_;
}
}
}
else
{
lean_object* v_name_893_; lean_object* v_opts_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___f_897_; uint8_t v___x_898_; 
lean_dec(v___x_880_);
lean_dec(v_toPure_863_);
v_name_893_ = lean_ctor_get(v_dep_873_, 0);
v_opts_894_ = lean_ctor_get(v_dep_873_, 4);
v___x_895_ = lean_box(v_reconfigure_866_);
lean_inc(v_opts_894_);
v___f_896_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed), 7, 6);
lean_closure_set(v___f_896_, 0, v_start_864_);
lean_closure_set(v___f_896_, 1, v_s_874_);
lean_closure_set(v___f_896_, 2, v_opts_894_);
lean_closure_set(v___f_896_, 3, v_leanOpts_865_);
lean_closure_set(v___f_896_, 4, v___x_895_);
lean_closure_set(v___f_896_, 5, v_inst_867_);
lean_inc_ref(v___f_896_);
lean_inc(v_toBind_870_);
lean_inc_ref(v_ws_875_);
lean_inc_ref(v_dep_873_);
lean_inc_ref(v_pkg_869_);
lean_inc(v_resolve_868_);
v___f_897_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11), 7, 6);
lean_closure_set(v___f_897_, 0, v_resolve_868_);
lean_closure_set(v___f_897_, 1, v_pkg_869_);
lean_closure_set(v___f_897_, 2, v_dep_873_);
lean_closure_set(v___f_897_, 3, v_ws_875_);
lean_closure_set(v___f_897_, 4, v_toBind_870_);
lean_closure_set(v___f_897_, 5, v___f_896_);
v___x_898_ = lean_name_eq(v_baseName_871_, v_name_893_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec_ref(v___f_897_);
lean_dec(v_inst_872_);
lean_dec(v_baseName_871_);
v___x_899_ = lean_box(0);
v___x_900_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(v_resolve_868_, v_pkg_869_, v_dep_873_, v_ws_875_, v_toBind_870_, v___f_896_, v___x_899_);
return v___x_900_;
}
else
{
lean_object* v___f_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v___f_896_);
lean_dec_ref(v_ws_875_);
lean_dec_ref(v_dep_873_);
lean_dec_ref(v_pkg_869_);
lean_dec(v_resolve_868_);
v___f_901_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12), 2, 1);
lean_closure_set(v___f_901_, 0, v___f_897_);
v___x_902_ = 0;
v___x_903_ = l_Lean_Name_toString(v_baseName_871_, v___x_902_);
v___x_904_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
v___x_906_ = lean_apply_2(v_inst_872_, lean_box(0), v___x_905_);
v___x_907_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v___x_906_, v___f_901_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___boxed(lean_object* v_toPure_908_, lean_object* v_start_909_, lean_object* v_leanOpts_910_, lean_object* v_reconfigure_911_, lean_object* v_inst_912_, lean_object* v_resolve_913_, lean_object* v_pkg_914_, lean_object* v_toBind_915_, lean_object* v_baseName_916_, lean_object* v_inst_917_, lean_object* v_dep_918_, lean_object* v_s_919_){
_start:
{
uint8_t v_reconfigure_boxed_920_; lean_object* v_res_921_; 
v_reconfigure_boxed_920_ = lean_unbox(v_reconfigure_911_);
v_res_921_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(v_toPure_908_, v_start_909_, v_leanOpts_910_, v_reconfigure_boxed_920_, v_inst_912_, v_resolve_913_, v_pkg_914_, v_toBind_915_, v_baseName_916_, v_inst_917_, v_dep_918_, v_s_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_stop_922_, lean_object* v_toPure_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_resolve_927_, lean_object* v_leanOpts_928_, lean_object* v_reconfigure_929_, lean_object* v_toBind_930_, lean_object* v___f_931_, lean_object* v___f_932_, lean_object* v_next_933_, lean_object* v_acc_934_, lean_object* v_h_935_, lean_object* v_G_936_){
_start:
{
uint8_t v_reconfigure_boxed_937_; lean_object* v_res_938_; 
v_reconfigure_boxed_937_ = lean_unbox(v_reconfigure_929_);
v_res_938_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_stop_922_, v_toPure_923_, v_inst_924_, v_inst_925_, v_inst_926_, v_resolve_927_, v_leanOpts_928_, v_reconfigure_boxed_937_, v_toBind_930_, v___f_931_, v___f_932_, v_next_933_, v_acc_934_, v_h_935_, v_G_936_);
lean_dec(v_stop_922_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object* v_pkg_939_, lean_object* v_toPure_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_resolve_944_, lean_object* v_leanOpts_945_, uint8_t v_reconfigure_946_, lean_object* v_toBind_947_, lean_object* v___f_948_, lean_object* v___f_949_, lean_object* v_start_950_, lean_object* v___f_951_, lean_object* v_____x_952_){
_start:
{
lean_object* v_ws_953_; lean_object* v_depIdxs_954_; lean_object* v_packages_955_; lean_object* v___f_956_; lean_object* v_stop_957_; lean_object* v___x_958_; lean_object* v___f_959_; lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_ws_953_ = lean_ctor_get(v_____x_952_, 0);
lean_inc_ref(v_ws_953_);
v_depIdxs_954_ = lean_ctor_get(v_____x_952_, 1);
lean_inc_ref(v_depIdxs_954_);
lean_dec_ref(v_____x_952_);
v_packages_955_ = lean_ctor_get(v_ws_953_, 4);
lean_inc_n(v_toPure_940_, 2);
v___f_956_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 4, 3);
lean_closure_set(v___f_956_, 0, v_depIdxs_954_);
lean_closure_set(v___f_956_, 1, v_pkg_939_);
lean_closure_set(v___f_956_, 2, v_toPure_940_);
v_stop_957_ = lean_array_get_size(v_packages_955_);
v___x_958_ = lean_box(v_reconfigure_946_);
lean_inc_n(v_toBind_947_, 2);
v___f_959_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 15, 11);
lean_closure_set(v___f_959_, 0, v_stop_957_);
lean_closure_set(v___f_959_, 1, v_toPure_940_);
lean_closure_set(v___f_959_, 2, v_inst_941_);
lean_closure_set(v___f_959_, 3, v_inst_942_);
lean_closure_set(v___f_959_, 4, v_inst_943_);
lean_closure_set(v___f_959_, 5, v_resolve_944_);
lean_closure_set(v___f_959_, 6, v_leanOpts_945_);
lean_closure_set(v___f_959_, 7, v___x_958_);
lean_closure_set(v___f_959_, 8, v_toBind_947_);
lean_closure_set(v___f_959_, 9, v___f_948_);
lean_closure_set(v___f_959_, 10, v___f_949_);
v___f_960_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 7, 6);
lean_closure_set(v___f_960_, 0, v___f_959_);
lean_closure_set(v___f_960_, 1, v_start_950_);
lean_closure_set(v___f_960_, 2, v_ws_953_);
lean_closure_set(v___f_960_, 3, v_toBind_947_);
lean_closure_set(v___f_960_, 4, v___f_951_);
lean_closure_set(v___f_960_, 5, v___f_956_);
v___x_961_ = lean_apply_2(v_toPure_940_, lean_box(0), lean_box(0));
v___x_962_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_961_, v___f_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object* v_pkg_963_, lean_object* v_toPure_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_resolve_968_, lean_object* v_leanOpts_969_, lean_object* v_reconfigure_970_, lean_object* v_toBind_971_, lean_object* v___f_972_, lean_object* v___f_973_, lean_object* v_start_974_, lean_object* v___f_975_, lean_object* v_____x_976_){
_start:
{
uint8_t v_reconfigure_boxed_977_; lean_object* v_res_978_; 
v_reconfigure_boxed_977_ = lean_unbox(v_reconfigure_970_);
v_res_978_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(v_pkg_963_, v_toPure_964_, v_inst_965_, v_inst_966_, v_inst_967_, v_resolve_968_, v_leanOpts_969_, v_reconfigure_boxed_977_, v_toBind_971_, v___f_972_, v___f_973_, v_start_974_, v___f_975_, v_____x_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_resolve_982_, lean_object* v_leanOpts_983_, uint8_t v_reconfigure_984_, lean_object* v_ws_985_, lean_object* v_wsIdx_986_){
_start:
{
lean_object* v_packages_987_; lean_object* v_pkg_988_; lean_object* v_toApplicative_989_; lean_object* v_baseName_990_; lean_object* v_depConfigs_991_; lean_object* v_toBind_992_; lean_object* v_toPure_993_; lean_object* v_start_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_s_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_packages_987_ = lean_ctor_get(v_ws_985_, 4);
v_pkg_988_ = lean_array_fget(v_packages_987_, v_wsIdx_986_);
v_toApplicative_989_ = lean_ctor_get(v_inst_979_, 0);
v_baseName_990_ = lean_ctor_get(v_pkg_988_, 1);
lean_inc(v_baseName_990_);
v_depConfigs_991_ = lean_ctor_get(v_pkg_988_, 12);
lean_inc_ref(v_depConfigs_991_);
v_toBind_992_ = lean_ctor_get(v_inst_979_, 1);
lean_inc_n(v_toBind_992_, 2);
v_toPure_993_ = lean_ctor_get(v_toApplicative_989_, 1);
v_start_994_ = lean_array_get_size(v_packages_987_);
v___x_995_ = lean_array_get_size(v_depConfigs_991_);
v___x_996_ = lean_mk_empty_array_with_capacity(v___x_995_);
v_s_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_997_, 0, v_ws_985_);
lean_ctor_set(v_s_997_, 1, v___x_996_);
lean_inc_n(v_toPure_993_, 4);
v___f_998_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_998_, 0, v_toPure_993_);
v___f_999_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_999_, 0, v_toPure_993_);
v___f_1000_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1000_, 0, v_toPure_993_);
v___x_1001_ = lean_box(v_reconfigure_984_);
lean_inc_ref(v_leanOpts_983_);
lean_inc(v_resolve_982_);
lean_inc(v_inst_981_);
lean_inc(v_inst_980_);
lean_inc_ref(v_inst_979_);
lean_inc(v_pkg_988_);
v___f_1002_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed), 14, 13);
lean_closure_set(v___f_1002_, 0, v_pkg_988_);
lean_closure_set(v___f_1002_, 1, v_toPure_993_);
lean_closure_set(v___f_1002_, 2, v_inst_979_);
lean_closure_set(v___f_1002_, 3, v_inst_980_);
lean_closure_set(v___f_1002_, 4, v_inst_981_);
lean_closure_set(v___f_1002_, 5, v_resolve_982_);
lean_closure_set(v___f_1002_, 6, v_leanOpts_983_);
lean_closure_set(v___f_1002_, 7, v___x_1001_);
lean_closure_set(v___f_1002_, 8, v_toBind_992_);
lean_closure_set(v___f_1002_, 9, v___f_1000_);
lean_closure_set(v___f_1002_, 10, v___f_998_);
lean_closure_set(v___f_1002_, 11, v_start_994_);
lean_closure_set(v___f_1002_, 12, v___f_999_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_nat_dec_lt(v___x_1003_, v___x_995_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc(v_toPure_993_);
lean_dec_ref(v_depConfigs_991_);
lean_dec(v_baseName_990_);
lean_dec(v_pkg_988_);
lean_dec_ref(v_leanOpts_983_);
lean_dec(v_resolve_982_);
lean_dec(v_inst_981_);
lean_dec(v_inst_980_);
lean_dec_ref(v_inst_979_);
v___x_1005_ = lean_apply_2(v_toPure_993_, lean_box(0), v_s_997_);
v___x_1006_ = lean_apply_4(v_toBind_992_, lean_box(0), lean_box(0), v___x_1005_, v___f_1002_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; lean_object* v___f_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = lean_box(v_reconfigure_984_);
lean_inc(v_toBind_992_);
lean_inc(v_toPure_993_);
v___f_1008_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___boxed), 12, 10);
lean_closure_set(v___f_1008_, 0, v_toPure_993_);
lean_closure_set(v___f_1008_, 1, v_start_994_);
lean_closure_set(v___f_1008_, 2, v_leanOpts_983_);
lean_closure_set(v___f_1008_, 3, v___x_1007_);
lean_closure_set(v___f_1008_, 4, v_inst_981_);
lean_closure_set(v___f_1008_, 5, v_resolve_982_);
lean_closure_set(v___f_1008_, 6, v_pkg_988_);
lean_closure_set(v___f_1008_, 7, v_toBind_992_);
lean_closure_set(v___f_1008_, 8, v_baseName_990_);
lean_closure_set(v___f_1008_, 9, v_inst_980_);
v___x_1009_ = lean_usize_of_nat(v___x_995_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_979_, v___f_1008_, v_depConfigs_991_, v___x_1009_, v___x_1010_, v_s_997_);
v___x_1012_ = lean_apply_4(v_toBind_992_, lean_box(0), lean_box(0), v___x_1011_, v___f_1002_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_stop_1013_, lean_object* v_toPure_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_resolve_1018_, lean_object* v_leanOpts_1019_, uint8_t v_reconfigure_1020_, lean_object* v_toBind_1021_, lean_object* v___f_1022_, lean_object* v___f_1023_, lean_object* v_next_1024_, lean_object* v_acc_1025_, lean_object* v_h_1026_, lean_object* v_G_1027_){
_start:
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_nat_dec_lt(v_next_1024_, v_stop_1013_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec(v_G_1027_);
lean_dec(v_next_1024_);
lean_dec(v___f_1023_);
lean_dec(v___f_1022_);
lean_dec(v_toBind_1021_);
lean_dec_ref(v_leanOpts_1019_);
lean_dec(v_resolve_1018_);
lean_dec(v_inst_1017_);
lean_dec(v_inst_1016_);
lean_dec_ref(v_inst_1015_);
v___x_1029_ = lean_apply_2(v_toPure_1014_, lean_box(0), v_acc_1025_);
return v___x_1029_;
}
else
{
lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc(v_next_1024_);
v___f_1030_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1030_, 0, v_toPure_1014_);
lean_closure_set(v___f_1030_, 1, v_next_1024_);
lean_closure_set(v___f_1030_, 2, v_G_1027_);
v___x_1031_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1015_, v_inst_1016_, v_inst_1017_, v_resolve_1018_, v_leanOpts_1019_, v_reconfigure_1020_, v_acc_1025_, v_next_1024_);
lean_dec(v_next_1024_);
lean_inc_n(v_toBind_1021_, 2);
v___x_1032_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1031_, v___f_1022_);
v___x_1033_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1032_, v___f_1023_);
v___x_1034_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1033_, v___f_1030_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_resolve_1038_, lean_object* v_leanOpts_1039_, lean_object* v_reconfigure_1040_, lean_object* v_ws_1041_, lean_object* v_wsIdx_1042_){
_start:
{
uint8_t v_reconfigure_boxed_1043_; lean_object* v_res_1044_; 
v_reconfigure_boxed_1043_ = lean_unbox(v_reconfigure_1040_);
v_res_1044_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1035_, v_inst_1036_, v_inst_1037_, v_resolve_1038_, v_leanOpts_1039_, v_reconfigure_boxed_1043_, v_ws_1041_, v_wsIdx_1042_);
lean_dec(v_wsIdx_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_resolve_1049_, lean_object* v_leanOpts_1050_, uint8_t v_reconfigure_1051_, lean_object* v_ws_1052_, lean_object* v_wsIdx_1053_, lean_object* v_h_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1046_, v_inst_1047_, v_inst_1048_, v_resolve_1049_, v_leanOpts_1050_, v_reconfigure_1051_, v_ws_1052_, v_wsIdx_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_resolve_1060_, lean_object* v_leanOpts_1061_, lean_object* v_reconfigure_1062_, lean_object* v_ws_1063_, lean_object* v_wsIdx_1064_, lean_object* v_h_1065_){
_start:
{
uint8_t v_reconfigure_boxed_1066_; lean_object* v_res_1067_; 
v_reconfigure_boxed_1066_ = lean_unbox(v_reconfigure_1062_);
v_res_1067_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1056_, v_inst_1057_, v_inst_1058_, v_inst_1059_, v_resolve_1060_, v_leanOpts_1061_, v_reconfigure_boxed_1066_, v_ws_1063_, v_wsIdx_1064_, v_h_1065_);
lean_dec(v_wsIdx_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_1068_, lean_object* v_h__1_1069_, lean_object* v_h__2_1070_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 1)
{
lean_object* v_val_1071_; lean_object* v___x_1072_; 
lean_dec(v_h__2_1070_);
v_val_1071_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_val_1071_);
lean_dec_ref(v_x_1068_);
v___x_1072_ = lean_apply_1(v_h__1_1069_, v_val_1071_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; 
lean_dec(v_h__1_1069_);
v___x_1073_ = lean_apply_2(v_h__2_1070_, v_x_1068_, lean_box(0));
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_1074_, lean_object* v_s_1075_, lean_object* v_motive_1076_, lean_object* v_x_1077_, lean_object* v_h__1_1078_, lean_object* v_h__2_1079_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__2_1079_);
v_val_1080_ = lean_ctor_get(v_x_1077_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v_x_1077_);
v___x_1081_ = lean_apply_1(v_h__1_1078_, v_val_1080_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_h__1_1078_);
v___x_1082_ = lean_apply_2(v_h__2_1079_, v_x_1077_, lean_box(0));
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1083_, lean_object* v_s_1084_, lean_object* v_motive_1085_, lean_object* v_x_1086_, lean_object* v_h__1_1087_, lean_object* v_h__2_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1083_, v_s_1084_, v_motive_1085_, v_x_1086_, v_h__1_1087_, v_h__2_1088_);
lean_dec_ref(v_s_1084_);
lean_dec_ref(v_ws_1083_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___redArg(lean_object* v_x_1090_, lean_object* v_h__1_1091_){
_start:
{
lean_object* v_ws_1092_; lean_object* v_depIdxs_1093_; lean_object* v___x_1094_; 
v_ws_1092_ = lean_ctor_get(v_x_1090_, 0);
lean_inc_ref(v_ws_1092_);
v_depIdxs_1093_ = lean_ctor_get(v_x_1090_, 1);
lean_inc_ref(v_depIdxs_1093_);
lean_dec_ref(v_x_1090_);
v___x_1094_ = lean_apply_4(v_h__1_1091_, v_ws_1092_, v_depIdxs_1093_, lean_box(0), lean_box(0));
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter(lean_object* v_ws_1095_, lean_object* v_motive_1096_, lean_object* v_x_1097_, lean_object* v_h__1_1098_){
_start:
{
lean_object* v_ws_1099_; lean_object* v_depIdxs_1100_; lean_object* v___x_1101_; 
v_ws_1099_ = lean_ctor_get(v_x_1097_, 0);
lean_inc_ref(v_ws_1099_);
v_depIdxs_1100_ = lean_ctor_get(v_x_1097_, 1);
lean_inc_ref(v_depIdxs_1100_);
lean_dec_ref(v_x_1097_);
v___x_1101_ = lean_apply_4(v_h__1_1098_, v_ws_1099_, v_depIdxs_1100_, lean_box(0), lean_box(0));
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___boxed(lean_object* v_ws_1102_, lean_object* v_motive_1103_, lean_object* v_x_1104_, lean_object* v_h__1_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter(v_ws_1102_, v_motive_1103_, v_x_1104_, v_h__1_1105_);
lean_dec_ref(v_ws_1102_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___redArg(lean_object* v_h__1_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_apply_1(v_h__1_1107_, lean_box(0));
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter(lean_object* v_ws_1109_, lean_object* v_motive_1110_, lean_object* v_x_1111_, lean_object* v_h__1_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_1(v_h__1_1112_, lean_box(0));
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___boxed(lean_object* v_ws_1114_, lean_object* v_motive_1115_, lean_object* v_x_1116_, lean_object* v_h__1_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter(v_ws_1114_, v_motive_1115_, v_x_1116_, v_h__1_1117_);
lean_dec_ref(v_ws_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1119_, lean_object* v_h__1_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_apply_2(v_h__1_1120_, v_x_1119_, lean_box(0));
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_stop_1122_, lean_object* v_motive_1123_, lean_object* v_x_1124_, lean_object* v_h__1_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_apply_2(v_h__1_1125_, v_x_1124_, lean_box(0));
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_stop_1127_, lean_object* v_motive_1128_, lean_object* v_x_1129_, lean_object* v_h__1_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_stop_1127_, v_motive_1128_, v_x_1129_, v_h__1_1130_);
lean_dec(v_stop_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_x_1132_, lean_object* v_h__1_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_apply_2(v_h__1_1133_, v_x_1132_, lean_box(0));
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1135_, lean_object* v_motive_1136_, lean_object* v_x_1137_, lean_object* v_h__1_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_apply_2(v_h__1_1138_, v_x_1137_, lean_box(0));
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1140_, lean_object* v_motive_1141_, lean_object* v_x_1142_, lean_object* v_h__1_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1140_, v_motive_1141_, v_x_1142_, v_h__1_1143_);
lean_dec_ref(v_ws_1140_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___redArg(lean_object* v_x_1145_, lean_object* v_h__1_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_apply_2(v_h__1_1146_, v_x_1145_, lean_box(0));
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter(lean_object* v_depIdxs_1148_, lean_object* v_motive_1149_, lean_object* v_x_1150_, lean_object* v_h__1_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_apply_2(v_h__1_1151_, v_x_1150_, lean_box(0));
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___boxed(lean_object* v_depIdxs_1153_, lean_object* v_motive_1154_, lean_object* v_x_1155_, lean_object* v_h__1_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter(v_depIdxs_1153_, v_motive_1154_, v_x_1155_, v_h__1_1156_);
lean_dec_ref(v_depIdxs_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_ws_1161_, lean_object* v_resolve_1162_, lean_object* v_root_1163_, lean_object* v_leanOpts_1164_, uint8_t v_reconfigure_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1158_, v_inst_1159_, v_inst_1160_, v_resolve_1162_, v_leanOpts_1164_, v_reconfigure_1165_, v_ws_1161_, v_root_1163_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_ws_1170_, lean_object* v_resolve_1171_, lean_object* v_root_1172_, lean_object* v_leanOpts_1173_, lean_object* v_reconfigure_1174_){
_start:
{
uint8_t v_reconfigure_boxed_1175_; lean_object* v_res_1176_; 
v_reconfigure_boxed_1175_ = lean_unbox(v_reconfigure_1174_);
v_res_1176_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1167_, v_inst_1168_, v_inst_1169_, v_ws_1170_, v_resolve_1171_, v_root_1172_, v_leanOpts_1173_, v_reconfigure_boxed_1175_);
lean_dec(v_root_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_ws_1181_, lean_object* v_resolve_1182_, lean_object* v_root_1183_, lean_object* v_h_1184_, lean_object* v_leanOpts_1185_, uint8_t v_reconfigure_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1178_, v_inst_1179_, v_inst_1180_, v_resolve_1182_, v_leanOpts_1185_, v_reconfigure_1186_, v_ws_1181_, v_root_1183_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_ws_1192_, lean_object* v_resolve_1193_, lean_object* v_root_1194_, lean_object* v_h_1195_, lean_object* v_leanOpts_1196_, lean_object* v_reconfigure_1197_){
_start:
{
uint8_t v_reconfigure_boxed_1198_; lean_object* v_res_1199_; 
v_reconfigure_boxed_1198_ = lean_unbox(v_reconfigure_1197_);
v_res_1199_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1188_, v_inst_1189_, v_inst_1190_, v_inst_1191_, v_ws_1192_, v_resolve_1193_, v_root_1194_, v_h_1195_, v_leanOpts_1196_, v_reconfigure_boxed_1198_);
lean_dec(v_root_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1200_, lean_object* v_init_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_apply_1(v_x_1200_, v_init_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1203_, lean_object* v_00_u03b1_1204_, lean_object* v_x_1205_, lean_object* v_init_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_apply_1(v_x_1205_, v_init_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object* v_toUpdate_1208_, lean_object* v_as_1209_, size_t v_i_1210_, size_t v_stop_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_fst_1216_; lean_object* v_snd_1217_; uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_eq(v_i_1210_, v_stop_1211_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; uint8_t v_inherited_1225_; 
v___x_1224_ = lean_array_uget_borrowed(v_as_1209_, v_i_1210_);
v_inherited_1225_ = lean_ctor_get_uint8(v___x_1224_, sizeof(void*)*5);
if (v_inherited_1225_ == 0)
{
lean_object* v_name_1226_; uint8_t v___x_1227_; 
v_name_1226_ = lean_ctor_get(v___x_1224_, 0);
v___x_1227_ = l_Lean_NameSet_contains(v_toUpdate_1208_, v_name_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_box(0);
lean_inc(v___x_1224_);
lean_inc(v_name_1226_);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1226_, v___x_1224_, v___y_1213_);
v_fst_1216_ = v___x_1228_;
v_snd_1217_ = v___x_1229_;
goto v___jp_1215_;
}
else
{
goto v___jp_1221_;
}
}
else
{
goto v___jp_1221_;
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_b_1212_);
lean_ctor_set(v___x_1230_, 1, v___y_1213_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
v___jp_1215_:
{
size_t v___x_1218_; size_t v___x_1219_; 
v___x_1218_ = ((size_t)1ULL);
v___x_1219_ = lean_usize_add(v_i_1210_, v___x_1218_);
v_i_1210_ = v___x_1219_;
v_b_1212_ = v_fst_1216_;
v___y_1213_ = v_snd_1217_;
goto _start;
}
v___jp_1221_:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_box(0);
v_fst_1216_ = v___x_1222_;
v_snd_1217_ = v___y_1213_;
goto v___jp_1215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object* v_toUpdate_1232_, lean_object* v_as_1233_, lean_object* v_i_1234_, lean_object* v_stop_1235_, lean_object* v_b_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
size_t v_i_boxed_1239_; size_t v_stop_boxed_1240_; lean_object* v_res_1241_; 
v_i_boxed_1239_ = lean_unbox_usize(v_i_1234_);
lean_dec(v_i_1234_);
v_stop_boxed_1240_ = lean_unbox_usize(v_stop_1235_);
lean_dec(v_stop_1235_);
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1232_, v_as_1233_, v_i_boxed_1239_, v_stop_boxed_1240_, v_b_1236_, v___y_1237_);
lean_dec_ref(v_as_1233_);
lean_dec(v_toUpdate_1232_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1242_, size_t v_i_1243_, size_t v_stop_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_eq(v_i_1243_, v_stop_1244_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; 
v___x_1249_ = lean_array_uget_borrowed(v_as_1242_, v_i_1243_);
lean_inc_ref(v___y_1246_);
lean_inc(v___x_1249_);
v___x_1250_ = lean_apply_2(v___y_1246_, v___x_1249_, lean_box(0));
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1243_, v___x_1251_);
v_i_1243_ = v___x_1252_;
v_b_1245_ = v___x_1250_;
goto _start;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_b_1245_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1255_, lean_object* v_i_1256_, lean_object* v_stop_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
size_t v_i_boxed_1261_; size_t v_stop_boxed_1262_; lean_object* v_res_1263_; 
v_i_boxed_1261_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v_stop_boxed_1262_ = lean_unbox_usize(v_stop_1257_);
lean_dec(v_stop_1257_);
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1255_, v_i_boxed_1261_, v_stop_boxed_1262_, v_b_1258_, v___y_1259_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v_as_1255_);
return v_res_1263_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1271_ = lean_array_get_size(v___x_1270_);
return v___x_1271_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_nat_dec_lt(v___x_1273_, v___x_1272_);
return v___x_1274_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1276_ = lean_nat_dec_le(v___x_1275_, v___x_1275_);
return v___x_1276_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8(void){
_start:
{
lean_object* v___x_1277_; size_t v___x_1278_; 
v___x_1277_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1278_ = lean_usize_of_nat(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1281_, lean_object* v_toUpdate_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___y_1287_; lean_object* v___y_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v_packages_1313_; lean_object* v___x_1314_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v_val_1319_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___x_1367_; lean_object* v_baseName_1368_; lean_object* v_dir_1369_; lean_object* v_config_1370_; lean_object* v_relManifestFile_1371_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v_fst_1376_; lean_object* v_snd_1377_; lean_object* v_packagesDir_x3f_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___x_1443_; lean_object* v_rootName_1444_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_val_1498_; lean_object* v___x_1524_; 
v_packages_1313_ = lean_ctor_get(v_ws_1281_, 4);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_fget_borrowed(v_packages_1313_, v___x_1314_);
v_baseName_1368_ = lean_ctor_get(v___x_1367_, 1);
v_dir_1369_ = lean_ctor_get(v___x_1367_, 4);
v_config_1370_ = lean_ctor_get(v___x_1367_, 6);
v_relManifestFile_1371_ = lean_ctor_get(v___x_1367_, 9);
v___x_1443_ = 0;
lean_inc(v_baseName_1368_);
v_rootName_1444_ = l_Lean_Name_toString(v_baseName_1368_, v___x_1443_);
lean_inc_ref(v_relManifestFile_1371_);
lean_inc_ref(v_dir_1369_);
v___x_1495_ = l_Lake_joinRelative(v_dir_1369_, v_relManifestFile_1371_);
v___x_1496_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1524_ = l_Lake_Manifest_load(v___x_1495_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 1);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
v_val_1498_ = v___x_1530_;
goto v___jp_1497_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
v_a_1533_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1524_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1524_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 0);
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
v_val_1498_ = v___x_1538_;
goto v___jp_1497_;
}
}
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___y_1287_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
v___jp_1291_:
{
if (lean_obj_tag(v_fst_1293_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_snd_1294_);
v_a_1295_ = lean_ctor_get(v_fst_1293_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_fst_1293_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1297_ = v_fst_1293_;
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v_fst_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1299_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1300_ = lean_io_error_to_string(v_a_1295_);
v___x_1301_ = lean_string_append(v___x_1299_, v___x_1300_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = 3;
v___x_1303_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*1, v___x_1302_);
lean_inc_ref(v___y_1292_);
v___x_1304_ = lean_apply_2(v___y_1292_, v___x_1303_, lean_box(0));
v___x_1305_ = lean_box(0);
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1305_);
v___x_1307_ = v___x_1297_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v_fst_1293_);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_snd_1294_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
v___jp_1315_:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_array_get_size(v___y_1318_);
v___x_1321_ = lean_nat_dec_lt(v___x_1314_, v___x_1320_);
if (v___x_1321_ == 0)
{
v___y_1292_ = v___y_1316_;
v_fst_1293_ = v_val_1319_;
v_snd_1294_ = v___y_1317_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_nat_dec_le(v___x_1320_, v___x_1320_);
if (v___x_1323_ == 0)
{
if (v___x_1321_ == 0)
{
v___y_1292_ = v___y_1316_;
v_fst_1293_ = v_val_1319_;
v_snd_1294_ = v___y_1317_;
goto v___jp_1291_;
}
else
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1320_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1318_, v___x_1324_, v___x_1325_, v___x_1322_, v___y_1316_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_dec_ref(v___x_1326_);
v___y_1292_ = v___y_1316_;
v_fst_1293_ = v_val_1319_;
v_snd_1294_ = v___y_1317_;
goto v___jp_1291_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_val_1319_);
lean_dec(v___y_1317_);
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = lean_usize_of_nat(v___x_1320_);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1318_, v___x_1335_, v___x_1336_, v___x_1322_, v___y_1316_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_dec_ref(v___x_1337_);
v___y_1292_ = v___y_1316_;
v_fst_1293_ = v_val_1319_;
v_snd_1294_ = v___y_1317_;
goto v___jp_1291_;
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v_val_1319_);
lean_dec(v___y_1317_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
v___jp_1346_:
{
if (lean_obj_tag(v___y_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v___y_1350_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___y_1350_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___y_1350_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___y_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 1);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
v___y_1316_ = v___y_1347_;
v___y_1317_ = v___y_1348_;
v___y_1318_ = v___y_1349_;
v_val_1319_ = v___x_1356_;
goto v___jp_1315_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___y_1350_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___y_1350_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___y_1350_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___y_1350_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 0);
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v___y_1316_ = v___y_1347_;
v___y_1317_ = v___y_1348_;
v___y_1318_ = v___y_1349_;
v_val_1319_ = v___x_1364_;
goto v___jp_1315_;
}
}
}
}
v___jp_1372_:
{
lean_object* v_toWorkspaceConfig_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_toWorkspaceConfig_1378_ = lean_ctor_get(v_config_1370_, 0);
v___x_1379_ = l_System_FilePath_normalize(v___y_1375_);
lean_inc_ref(v_toWorkspaceConfig_1378_);
v___x_1380_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1378_);
lean_inc_ref(v___x_1380_);
v___x_1381_ = l_System_FilePath_normalize(v___x_1380_);
v___x_1382_ = lean_string_dec_eq(v___x_1379_, v___x_1381_);
lean_dec_ref(v___x_1381_);
lean_dec_ref(v___x_1379_);
if (v___x_1382_ == 0)
{
if (v_fst_1376_ == 0)
{
lean_dec_ref(v___x_1380_);
lean_dec_ref(v___y_1374_);
v___y_1287_ = v_snd_1377_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1383_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1384_ = lean_string_append(v___x_1383_, v___y_1374_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
lean_inc_ref(v_dir_1369_);
v___x_1387_ = l_Lake_joinRelative(v_dir_1369_, v___x_1380_);
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
v___x_1389_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
v___x_1391_ = 1;
v___x_1392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*1, v___x_1391_);
lean_inc_ref(v___y_1373_);
v___x_1393_ = lean_apply_2(v___y_1373_, v___x_1392_, lean_box(0));
v___x_1394_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1387_);
v___x_1395_ = l_Lake_createParentDirs(v___x_1387_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v___x_1395_);
v___x_1396_ = lean_io_rename(v___y_1374_, v___x_1387_);
lean_dec_ref(v___x_1387_);
lean_dec_ref(v___y_1374_);
v___y_1347_ = v___y_1373_;
v___y_1348_ = v_snd_1377_;
v___y_1349_ = v___x_1394_;
v___y_1350_ = v___x_1396_;
goto v___jp_1346_;
}
else
{
lean_dec_ref(v___x_1387_);
lean_dec_ref(v___y_1374_);
v___y_1347_ = v___y_1373_;
v___y_1348_ = v_snd_1377_;
v___y_1349_ = v___x_1394_;
v___y_1350_ = v___x_1395_;
goto v___jp_1346_;
}
}
}
else
{
lean_dec_ref(v___x_1380_);
lean_dec_ref(v___y_1374_);
v___y_1287_ = v_snd_1377_;
goto v___jp_1286_;
}
}
v___jp_1397_:
{
if (lean_obj_tag(v_packagesDir_x3f_1398_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_val_1401_ = lean_ctor_get(v_packagesDir_x3f_1398_, 0);
lean_inc_n(v_val_1401_, 2);
lean_dec_ref(v_packagesDir_x3f_1398_);
lean_inc_ref(v_dir_1369_);
v___x_1402_ = l_Lake_joinRelative(v_dir_1369_, v_val_1401_);
v___x_1403_ = l_System_FilePath_pathExists(v___x_1402_);
v___x_1404_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1405_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1405_ == 0)
{
v___y_1373_ = v___y_1400_;
v___y_1374_ = v___x_1402_;
v___y_1375_ = v_val_1401_;
v_fst_1376_ = v___x_1403_;
v_snd_1377_ = v___y_1399_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1407_ == 0)
{
if (v___x_1405_ == 0)
{
v___y_1373_ = v___y_1400_;
v___y_1374_ = v___x_1402_;
v___y_1375_ = v_val_1401_;
v_fst_1376_ = v___x_1403_;
v_snd_1377_ = v___y_1399_;
goto v___jp_1372_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1404_, v___x_1408_, v___x_1409_, v___x_1406_, v___y_1400_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_dec_ref(v___x_1410_);
v___y_1373_ = v___y_1400_;
v___y_1374_ = v___x_1402_;
v___y_1375_ = v_val_1401_;
v_fst_1376_ = v___x_1403_;
v_snd_1377_ = v___y_1399_;
goto v___jp_1372_;
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v___x_1402_);
lean_dec(v_val_1401_);
lean_dec(v___y_1399_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1404_, v___x_1419_, v___x_1420_, v___x_1406_, v___y_1400_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec_ref(v___x_1421_);
v___y_1373_ = v___y_1400_;
v___y_1374_ = v___x_1402_;
v___y_1375_ = v_val_1401_;
v_fst_1376_ = v___x_1403_;
v_snd_1377_ = v___y_1399_;
goto v___jp_1372_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___x_1402_);
lean_dec(v_val_1401_);
lean_dec(v___y_1399_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v_packagesDir_x3f_1398_);
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___y_1399_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
v___jp_1433_:
{
lean_object* v_packagesDir_x3f_1437_; 
v_packagesDir_x3f_1437_ = lean_ctor_get(v___y_1434_, 2);
lean_inc(v_packagesDir_x3f_1437_);
lean_dec_ref(v___y_1434_);
v_packagesDir_x3f_1398_ = v_packagesDir_x3f_1437_;
v___y_1399_ = v___y_1435_;
v___y_1400_ = v___y_1436_;
goto v___jp_1397_;
}
v___jp_1438_:
{
if (lean_obj_tag(v___y_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_snd_1442_; 
v_a_1441_ = lean_ctor_get(v___y_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref(v___y_1440_);
v_snd_1442_ = lean_ctor_get(v_a_1441_, 1);
lean_inc(v_snd_1442_);
lean_dec(v_a_1441_);
v___y_1434_ = v___y_1439_;
v___y_1435_ = v_snd_1442_;
v___y_1436_ = v_a_1284_;
goto v___jp_1433_;
}
else
{
lean_dec_ref(v___y_1439_);
return v___y_1440_;
}
}
v___jp_1445_:
{
if (lean_obj_tag(v_fst_1446_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1480_; 
v_a_1448_ = lean_ctor_get(v_fst_1446_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_fst_1446_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1450_ = v_fst_1446_;
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v_fst_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
if (lean_obj_tag(v_a_1448_) == 11)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec_ref(v_a_1448_);
v___x_1452_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1453_ = lean_string_append(v_rootName_1444_, v___x_1452_);
v___x_1454_ = 1;
v___x_1455_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set_uint8(v___x_1455_, sizeof(void*)*1, v___x_1454_);
lean_inc_ref(v_a_1284_);
v___x_1456_ = lean_apply_2(v_a_1284_, v___x_1455_, lean_box(0));
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v_snd_1447_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1457_);
v___x_1459_ = v___x_1450_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1282_) == 0)
{
lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec(v_snd_1447_);
lean_dec_ref(v_rootName_1444_);
v___x_1461_ = lean_io_error_to_string(v_a_1448_);
v___x_1462_ = 3;
v___x_1463_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*1, v___x_1462_);
lean_inc_ref(v_a_1284_);
v___x_1464_ = lean_apply_2(v_a_1284_, v___x_1463_, lean_box(0));
v___x_1465_ = lean_box(0);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 1);
lean_ctor_set(v___x_1450_, 0, v___x_1465_);
v___x_1467_ = v___x_1450_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1469_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_1470_ = lean_string_append(v_rootName_1444_, v___x_1469_);
v___x_1471_ = lean_io_error_to_string(v_a_1448_);
v___x_1472_ = lean_string_append(v___x_1470_, v___x_1471_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = 2;
v___x_1474_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*1, v___x_1473_);
lean_inc_ref(v_a_1284_);
v___x_1475_ = lean_apply_2(v_a_1284_, v___x_1474_, lean_box(0));
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v_snd_1447_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1476_);
v___x_1478_ = v___x_1450_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1444_);
if (lean_obj_tag(v_toUpdate_1282_) == 0)
{
lean_object* v_a_1481_; lean_object* v_packagesDir_x3f_1482_; lean_object* v_packages_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_a_1481_ = lean_ctor_get(v_fst_1446_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v_fst_1446_);
v_packagesDir_x3f_1482_ = lean_ctor_get(v_a_1481_, 2);
v_packages_1483_ = lean_ctor_get(v_a_1481_, 3);
v___x_1484_ = lean_array_get_size(v_packages_1483_);
v___x_1485_ = lean_nat_dec_lt(v___x_1314_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_inc(v_packagesDir_x3f_1482_);
lean_dec(v_a_1481_);
v_packagesDir_x3f_1398_ = v_packagesDir_x3f_1482_;
v___y_1399_ = v_snd_1447_;
v___y_1400_ = v_a_1284_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_nat_dec_le(v___x_1484_, v___x_1484_);
if (v___x_1487_ == 0)
{
if (v___x_1485_ == 0)
{
lean_inc(v_packagesDir_x3f_1482_);
lean_dec(v_a_1481_);
v_packagesDir_x3f_1398_ = v_packagesDir_x3f_1482_;
v___y_1399_ = v_snd_1447_;
v___y_1400_ = v_a_1284_;
goto v___jp_1397_;
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1484_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1282_, v_packages_1483_, v___x_1488_, v___x_1489_, v___x_1486_, v_snd_1447_);
v___y_1439_ = v_a_1481_;
v___y_1440_ = v___x_1490_;
goto v___jp_1438_;
}
}
else
{
size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = lean_usize_of_nat(v___x_1484_);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1282_, v_packages_1483_, v___x_1491_, v___x_1492_, v___x_1486_, v_snd_1447_);
v___y_1439_ = v_a_1481_;
v___y_1440_ = v___x_1493_;
goto v___jp_1438_;
}
}
}
else
{
lean_object* v_a_1494_; 
v_a_1494_ = lean_ctor_get(v_fst_1446_, 0);
lean_inc(v_a_1494_);
lean_dec_ref(v_fst_1446_);
v___y_1434_ = v_a_1494_;
v___y_1435_ = v_snd_1447_;
v___y_1436_ = v_a_1284_;
goto v___jp_1433_;
}
}
}
v___jp_1497_:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1499_ == 0)
{
v_fst_1446_ = v_val_1498_;
v_snd_1447_ = v_a_1283_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1501_ == 0)
{
if (v___x_1499_ == 0)
{
v_fst_1446_ = v_val_1498_;
v_snd_1447_ = v_a_1283_;
goto v___jp_1445_;
}
else
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((size_t)0ULL);
v___x_1503_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1496_, v___x_1502_, v___x_1503_, v___x_1500_, v_a_1284_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_dec_ref(v___x_1504_);
v_fst_1446_ = v_val_1498_;
v_snd_1447_ = v_a_1283_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v_val_1498_);
lean_dec_ref(v_rootName_1444_);
lean_dec(v_a_1283_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1496_, v___x_1513_, v___x_1514_, v___x_1500_, v_a_1284_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_dec_ref(v___x_1515_);
v_fst_1446_ = v_val_1498_;
v_snd_1447_ = v_a_1283_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v_val_1498_);
lean_dec_ref(v_rootName_1444_);
lean_dec(v_a_1283_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1541_, lean_object* v_toUpdate_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1541_, v_toUpdate_1542_, v_a_1543_, v_a_1544_);
lean_dec_ref(v_a_1544_);
lean_dec(v_toUpdate_1542_);
lean_dec_ref(v_ws_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_toUpdate_1547_, lean_object* v_as_1548_, size_t v_i_1549_, size_t v_stop_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1547_, v_as_1548_, v_i_1549_, v_stop_1550_, v_b_1551_, v___y_1552_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_toUpdate_1556_, lean_object* v_as_1557_, lean_object* v_i_1558_, lean_object* v_stop_1559_, lean_object* v_b_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
size_t v_i_boxed_1564_; size_t v_stop_boxed_1565_; lean_object* v_res_1566_; 
v_i_boxed_1564_ = lean_unbox_usize(v_i_1558_);
lean_dec(v_i_1558_);
v_stop_boxed_1565_ = lean_unbox_usize(v_stop_1559_);
lean_dec(v_stop_1559_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_toUpdate_1556_, v_as_1557_, v_i_boxed_1564_, v_stop_boxed_1565_, v_b_1560_, v___y_1561_, v___y_1562_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v_as_1557_);
lean_dec(v_toUpdate_1556_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1567_, lean_object* v_as_1568_, size_t v_i_1569_, size_t v_stop_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_fst_1575_; lean_object* v_snd_1576_; lean_object* v___y_1581_; lean_object* v_name_1582_; uint8_t v___x_1585_; 
v___x_1585_ = lean_usize_dec_eq(v_i_1569_, v_stop_1570_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v_name_1587_; lean_object* v_scope_1588_; lean_object* v_configFile_1589_; lean_object* v_manifestFile_x3f_1590_; lean_object* v_src_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1614_; 
v___x_1586_ = lean_array_uget(v_as_1568_, v_i_1569_);
v_name_1587_ = lean_ctor_get(v___x_1586_, 0);
v_scope_1588_ = lean_ctor_get(v___x_1586_, 1);
v_configFile_1589_ = lean_ctor_get(v___x_1586_, 2);
v_manifestFile_x3f_1590_ = lean_ctor_get(v___x_1586_, 3);
v_src_1591_ = lean_ctor_get(v___x_1586_, 4);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1593_ = v___x_1586_;
v_isShared_1594_ = v_isSharedCheck_1614_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_src_1591_);
lean_inc(v_manifestFile_x3f_1590_);
lean_inc(v_configFile_1589_);
lean_inc(v_scope_1588_);
lean_inc(v_name_1587_);
lean_dec(v___x_1586_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1614_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1587_, v___y_1572_);
if (v___x_1595_ == 0)
{
uint8_t v___x_1596_; 
v___x_1596_ = 1;
if (lean_obj_tag(v_src_1591_) == 0)
{
lean_object* v_dir_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1609_; 
v_dir_1597_ = lean_ctor_get(v_src_1591_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_src_1591_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1599_ = v_src_1591_;
v_isShared_1600_ = v_isSharedCheck_1609_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_dir_1597_);
lean_dec(v_src_1591_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1609_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_relPkgDir_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v_relPkgDir_1601_ = lean_ctor_get(v_dep_1567_, 1);
lean_inc_ref(v_relPkgDir_1601_);
v___x_1602_ = l_Lake_joinRelative(v_relPkgDir_1601_, v_dir_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
lean_inc(v_name_1587_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v___x_1604_);
v___x_1606_ = v___x_1593_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_name_1587_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_scope_1588_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_configFile_1589_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_manifestFile_x3f_1590_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*5, v___x_1596_);
v___y_1581_ = v___x_1606_;
v_name_1582_ = v_name_1587_;
goto v___jp_1580_;
}
}
}
}
else
{
lean_object* v___x_1611_; 
lean_inc(v_name_1587_);
if (v_isShared_1594_ == 0)
{
v___x_1611_ = v___x_1593_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_name_1587_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_scope_1588_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_configFile_1589_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_manifestFile_x3f_1590_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_src_1591_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*5, v___x_1596_);
v___y_1581_ = v___x_1611_;
v_name_1582_ = v_name_1587_;
goto v___jp_1580_;
}
}
}
else
{
lean_object* v___x_1613_; 
lean_del_object(v___x_1593_);
lean_dec_ref(v_src_1591_);
lean_dec(v_manifestFile_x3f_1590_);
lean_dec_ref(v_configFile_1589_);
lean_dec_ref(v_scope_1588_);
lean_dec(v_name_1587_);
v___x_1613_ = lean_box(0);
v_fst_1575_ = v___x_1613_;
v_snd_1576_ = v___y_1572_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref(v_dep_1567_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_b_1571_);
lean_ctor_set(v___x_1615_, 1, v___y_1572_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
v___jp_1574_:
{
size_t v___x_1577_; size_t v___x_1578_; 
v___x_1577_ = ((size_t)1ULL);
v___x_1578_ = lean_usize_add(v_i_1569_, v___x_1577_);
v_i_1569_ = v___x_1578_;
v_b_1571_ = v_fst_1575_;
v___y_1572_ = v_snd_1576_;
goto _start;
}
v___jp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1582_, v___y_1581_, v___y_1572_);
v_fst_1575_ = v___x_1583_;
v_snd_1576_ = v___x_1584_;
goto v___jp_1574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1617_, lean_object* v_as_1618_, lean_object* v_i_1619_, lean_object* v_stop_1620_, lean_object* v_b_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
size_t v_i_boxed_1624_; size_t v_stop_boxed_1625_; lean_object* v_res_1626_; 
v_i_boxed_1624_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_stop_boxed_1625_ = lean_unbox_usize(v_stop_1620_);
lean_dec(v_stop_1620_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1617_, v_as_1618_, v_i_boxed_1624_, v_stop_boxed_1625_, v_b_1621_, v___y_1622_);
lean_dec_ref(v_as_1618_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_manifestEntry_1633_; lean_object* v_pkgDir_1634_; lean_object* v_name_1635_; lean_object* v_manifestFile_x3f_1636_; lean_object* v___y_1638_; lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v_val_1700_; lean_object* v___y_1728_; 
v_manifestEntry_1633_ = lean_ctor_get(v_dep_1629_, 4);
v_pkgDir_1634_ = lean_ctor_get(v_dep_1629_, 0);
v_name_1635_ = lean_ctor_get(v_manifestEntry_1633_, 0);
v_manifestFile_x3f_1636_ = lean_ctor_get(v_manifestEntry_1633_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1636_) == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1634_);
v___x_1749_ = l_Lake_joinRelative(v_pkgDir_1634_, v___x_1748_);
v___y_1728_ = v___x_1749_;
goto v___jp_1727_;
}
else
{
lean_object* v_val_1750_; lean_object* v___x_1751_; 
v_val_1750_ = lean_ctor_get(v_manifestFile_x3f_1636_, 0);
lean_inc(v_val_1750_);
lean_inc_ref(v_pkgDir_1634_);
v___x_1751_ = l_Lake_joinRelative(v_pkgDir_1634_, v_val_1750_);
v___y_1728_ = v___x_1751_;
goto v___jp_1727_;
}
v___jp_1637_:
{
if (lean_obj_tag(v_fst_1639_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1670_; 
lean_inc(v_name_1635_);
lean_dec_ref(v_dep_1629_);
v_a_1641_ = lean_ctor_get(v_fst_1639_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_fst_1639_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1643_ = v_fst_1639_;
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v_fst_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
if (lean_obj_tag(v_a_1641_) == 11)
{
uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_dec_ref(v_a_1641_);
v___x_1645_ = 0;
v___x_1646_ = l_Lean_Name_toString(v_name_1635_, v___x_1645_);
v___x_1647_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1648_ = lean_string_append(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_string_append(v___x_1648_, v___y_1638_);
lean_dec_ref(v___y_1638_);
v___x_1650_ = 2;
v___x_1651_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*1, v___x_1650_);
lean_inc_ref(v_a_1631_);
v___x_1652_ = lean_apply_2(v_a_1631_, v___x_1651_, lean_box(0));
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v_snd_1640_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1653_);
v___x_1655_ = v___x_1643_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
else
{
uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec_ref(v___y_1638_);
v___x_1657_ = 0;
v___x_1658_ = l_Lean_Name_toString(v_name_1635_, v___x_1657_);
v___x_1659_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1660_ = lean_string_append(v___x_1658_, v___x_1659_);
v___x_1661_ = lean_io_error_to_string(v_a_1641_);
v___x_1662_ = lean_string_append(v___x_1660_, v___x_1661_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = 2;
v___x_1664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set_uint8(v___x_1664_, sizeof(void*)*1, v___x_1663_);
lean_inc_ref(v_a_1631_);
v___x_1665_ = lean_apply_2(v_a_1631_, v___x_1664_, lean_box(0));
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v_snd_1640_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1666_);
v___x_1668_ = v___x_1643_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v___y_1638_);
v_a_1671_ = lean_ctor_get(v_fst_1639_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_fst_1639_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1673_ = v_fst_1639_;
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v_fst_1639_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_packages_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_packages_1675_ = lean_ctor_get(v_a_1671_, 3);
lean_inc_ref(v_packages_1675_);
lean_dec(v_a_1671_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_array_get_size(v_packages_1675_);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
lean_dec_ref(v_packages_1675_);
lean_dec_ref(v_dep_1629_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v_snd_1640_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1680_);
v___x_1682_ = v___x_1673_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_le(v___x_1677_, v___x_1677_);
if (v___x_1684_ == 0)
{
if (v___x_1679_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec_ref(v_packages_1675_);
lean_dec_ref(v_dep_1629_);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1678_);
lean_ctor_set(v___x_1685_, 1, v_snd_1640_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1685_);
v___x_1687_ = v___x_1673_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
lean_del_object(v___x_1673_);
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_of_nat(v___x_1677_);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1629_, v_packages_1675_, v___x_1689_, v___x_1690_, v___x_1678_, v_snd_1640_);
lean_dec_ref(v_packages_1675_);
return v___x_1691_;
}
}
else
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
lean_del_object(v___x_1673_);
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1677_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1629_, v_packages_1675_, v___x_1692_, v___x_1693_, v___x_1678_, v_snd_1640_);
lean_dec_ref(v_packages_1675_);
return v___x_1694_;
}
}
}
}
}
v___jp_1696_:
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = lean_array_get_size(v___y_1699_);
v___x_1702_ = lean_nat_dec_lt(v___y_1698_, v___x_1701_);
if (v___x_1702_ == 0)
{
v___y_1638_ = v___y_1697_;
v_fst_1639_ = v_val_1700_;
v_snd_1640_ = v_a_1630_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_nat_dec_le(v___x_1701_, v___x_1701_);
if (v___x_1704_ == 0)
{
if (v___x_1702_ == 0)
{
v___y_1638_ = v___y_1697_;
v_fst_1639_ = v_val_1700_;
v_snd_1640_ = v_a_1630_;
goto v___jp_1637_;
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1701_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1699_, v___x_1705_, v___x_1706_, v___x_1703_, v_a_1631_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref(v___x_1707_);
v___y_1638_ = v___y_1697_;
v_fst_1639_ = v_val_1700_;
v_snd_1640_ = v_a_1630_;
goto v___jp_1637_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v_val_1700_);
lean_dec_ref(v___y_1697_);
lean_dec(v_a_1630_);
lean_dec_ref(v_dep_1629_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
else
{
size_t v___x_1716_; size_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = ((size_t)0ULL);
v___x_1717_ = lean_usize_of_nat(v___x_1701_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1699_, v___x_1716_, v___x_1717_, v___x_1703_, v_a_1631_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_dec_ref(v___x_1718_);
v___y_1638_ = v___y_1697_;
v_fst_1639_ = v_val_1700_;
v_snd_1640_ = v_a_1630_;
goto v___jp_1637_;
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_val_1700_);
lean_dec_ref(v___y_1697_);
lean_dec(v_a_1630_);
lean_dec_ref(v_dep_1629_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
}
v___jp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1728_);
v___x_1731_ = l_Lake_Manifest_load(v___y_1728_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 1);
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
v___y_1697_ = v___y_1728_;
v___y_1698_ = v___x_1729_;
v___y_1699_ = v___x_1730_;
v_val_1700_ = v___x_1737_;
goto v___jp_1696_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1731_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1731_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
v___y_1697_ = v___y_1728_;
v___y_1698_ = v___x_1729_;
v___y_1699_ = v___x_1730_;
v_val_1700_ = v___x_1745_;
goto v___jp_1696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1752_, v_a_1753_, v_a_1754_);
lean_dec_ref(v_a_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1757_, lean_object* v_as_1758_, size_t v_i_1759_, size_t v_stop_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1757_, v_as_1758_, v_i_1759_, v_stop_1760_, v_b_1761_, v___y_1762_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1766_, lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_stop_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
size_t v_i_boxed_1774_; size_t v_stop_boxed_1775_; lean_object* v_res_1776_; 
v_i_boxed_1774_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_stop_boxed_1775_ = lean_unbox_usize(v_stop_1769_);
lean_dec(v_stop_1769_);
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1766_, v_as_1767_, v_i_boxed_1774_, v_stop_boxed_1775_, v_b_1770_, v___y_1771_, v___y_1772_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v_as_1767_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1778_, lean_object* v_pkg_1779_, lean_object* v_dep_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
uint8_t v___y_1785_; lean_object* v___y_1786_; lean_object* v_name_1816_; lean_object* v___x_1817_; 
v_name_1816_ = lean_ctor_get(v_dep_1780_, 0);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1781_, v_name_1816_);
if (lean_obj_tag(v___x_1817_) == 1)
{
lean_object* v_val_1818_; lean_object* v_lakeEnv_1819_; lean_object* v_packages_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_config_1823_; lean_object* v_dir_1824_; lean_object* v_toWorkspaceConfig_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_dep_1780_);
lean_dec_ref(v_pkg_1779_);
v_val_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_val_1818_);
lean_dec_ref(v___x_1817_);
v_lakeEnv_1819_ = lean_ctor_get(v_ws_1778_, 0);
lean_inc_ref(v_lakeEnv_1819_);
v_packages_1820_ = lean_ctor_get(v_ws_1778_, 4);
lean_inc_ref(v_packages_1820_);
lean_dec_ref(v_ws_1778_);
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = lean_array_fget(v_packages_1820_, v___x_1821_);
lean_dec_ref(v_packages_1820_);
v_config_1823_ = lean_ctor_get(v___x_1822_, 6);
lean_inc_ref(v_config_1823_);
v_dir_1824_ = lean_ctor_get(v___x_1822_, 4);
lean_inc_ref(v_dir_1824_);
lean_dec(v___x_1822_);
v_toWorkspaceConfig_1825_ = lean_ctor_get(v_config_1823_, 0);
lean_inc_ref(v_toWorkspaceConfig_1825_);
lean_dec_ref(v_config_1823_);
v___x_1826_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1825_);
v___x_1827_ = l_Lake_PackageEntry_materialize(v_val_1818_, v_lakeEnv_1819_, v_dir_1824_, v___x_1826_, v_a_1782_);
lean_dec_ref(v_lakeEnv_1819_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v_a_1828_);
lean_ctor_set(v___x_1832_, 1, v_a_1781_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_a_1781_);
v_a_1837_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1827_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1827_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_wsIdx_1845_; lean_object* v_relDir_1846_; uint8_t v___y_1848_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
lean_dec(v___x_1817_);
v_wsIdx_1845_ = lean_ctor_get(v_pkg_1779_, 0);
lean_inc(v_wsIdx_1845_);
v_relDir_1846_ = lean_ctor_get(v_pkg_1779_, 5);
lean_inc_ref(v_relDir_1846_);
lean_dec_ref(v_pkg_1779_);
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_nat_dec_eq(v_wsIdx_1845_, v___x_1852_);
lean_dec(v_wsIdx_1845_);
if (v___x_1853_ == 0)
{
uint8_t v___x_1854_; 
v___x_1854_ = 1;
v___y_1848_ = v___x_1854_;
goto v___jp_1847_;
}
else
{
uint8_t v___x_1855_; 
v___x_1855_ = 0;
v___y_1848_ = v___x_1855_;
goto v___jp_1847_;
}
v___jp_1847_:
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1850_ = lean_string_dec_eq(v_relDir_1846_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lake_joinRelative(v_relDir_1846_, v___x_1849_);
v___y_1785_ = v___y_1848_;
v___y_1786_ = v___x_1851_;
goto v___jp_1784_;
}
else
{
v___y_1785_ = v___y_1848_;
v___y_1786_ = v_relDir_1846_;
goto v___jp_1784_;
}
}
}
v___jp_1784_:
{
lean_object* v_lakeEnv_1787_; lean_object* v_packages_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_config_1791_; lean_object* v_dir_1792_; lean_object* v_toWorkspaceConfig_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_lakeEnv_1787_ = lean_ctor_get(v_ws_1778_, 0);
lean_inc_ref(v_lakeEnv_1787_);
v_packages_1788_ = lean_ctor_get(v_ws_1778_, 4);
lean_inc_ref(v_packages_1788_);
lean_dec_ref(v_ws_1778_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_array_fget(v_packages_1788_, v___x_1789_);
lean_dec_ref(v_packages_1788_);
v_config_1791_ = lean_ctor_get(v___x_1790_, 6);
lean_inc_ref(v_config_1791_);
v_dir_1792_ = lean_ctor_get(v___x_1790_, 4);
lean_inc_ref(v_dir_1792_);
lean_dec(v___x_1790_);
v_toWorkspaceConfig_1793_ = lean_ctor_get(v_config_1791_, 0);
lean_inc_ref(v_toWorkspaceConfig_1793_);
lean_dec_ref(v_config_1791_);
v___x_1794_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1793_);
v___x_1795_ = l_Lake_Dependency_materialize(v_dep_1780_, v___y_1785_, v_lakeEnv_1787_, v_dir_1792_, v___x_1794_, v___y_1786_, v_a_1782_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1807_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_manifestEntry_1800_; lean_object* v_name_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v_manifestEntry_1800_ = lean_ctor_get(v_a_1796_, 4);
v_name_1801_ = lean_ctor_get(v_manifestEntry_1800_, 0);
lean_inc_ref(v_manifestEntry_1800_);
lean_inc(v_name_1801_);
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1801_, v_manifestEntry_1800_, v_a_1781_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1796_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1803_);
v___x_1805_ = v___x_1798_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_a_1781_);
v_a_1808_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1795_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1795_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1856_, lean_object* v_pkg_1857_, lean_object* v_dep_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1856_, v_pkg_1857_, v_dep_1858_, v_a_1859_, v_a_1860_);
lean_dec_ref(v_a_1860_);
return v_res_1862_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1863_; 
v___x_1863_ = 4;
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1864_, lean_object* v_tc_x3f_1865_, uint8_t v_fixed_1866_, lean_object* v_self_1867_){
_start:
{
lean_object* v_clashes_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_clashes_1868_ = lean_ctor_get(v_self_1867_, 2);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_self_1867_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; lean_object* v_unused_1877_; 
v_unused_1876_ = lean_ctor_get(v_self_1867_, 1);
lean_dec(v_unused_1876_);
v_unused_1877_ = lean_ctor_get(v_self_1867_, 0);
lean_dec(v_unused_1877_);
v___x_1870_ = v_self_1867_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_clashes_1868_);
lean_dec(v_self_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v_tc_x3f_1865_);
lean_ctor_set(v___x_1870_, 0, v_src_1864_);
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_src_1864_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_tc_x3f_1865_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_clashes_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_ctor_set_uint8(v___x_1873_, sizeof(void*)*3, v_fixed_1866_);
return v___x_1873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1878_, lean_object* v_tc_x3f_1879_, lean_object* v_fixed_1880_, lean_object* v_self_1881_){
_start:
{
uint8_t v_fixed_boxed_1882_; lean_object* v_res_1883_; 
v_fixed_boxed_1882_ = lean_unbox(v_fixed_1880_);
v_res_1883_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1878_, v_tc_x3f_1879_, v_fixed_boxed_1882_, v_self_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1884_, lean_object* v_ver_1885_, uint8_t v_fixed_1886_, lean_object* v_self_1887_){
_start:
{
lean_object* v_src_1888_; lean_object* v_tc_x3f_1889_; lean_object* v_clashes_1890_; uint8_t v_fixed_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1900_; 
v_src_1888_ = lean_ctor_get(v_self_1887_, 0);
v_tc_x3f_1889_ = lean_ctor_get(v_self_1887_, 1);
v_clashes_1890_ = lean_ctor_get(v_self_1887_, 2);
v_fixed_1891_ = lean_ctor_get_uint8(v_self_1887_, sizeof(void*)*3);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_self_1887_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1893_ = v_self_1887_;
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_clashes_1890_);
lean_inc(v_tc_x3f_1889_);
lean_inc(v_src_1888_);
lean_dec(v_self_1887_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1895_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1895_, 0, v_src_1884_);
lean_ctor_set(v___x_1895_, 1, v_ver_1885_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*2, v_fixed_1886_);
v___x_1896_ = lean_array_push(v_clashes_1890_, v___x_1895_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 2, v___x_1896_);
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_src_1888_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_tc_x3f_1889_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___x_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*3, v_fixed_1891_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1901_, lean_object* v_ver_1902_, lean_object* v_fixed_1903_, lean_object* v_self_1904_){
_start:
{
uint8_t v_fixed_boxed_1905_; lean_object* v_res_1906_; 
v_fixed_boxed_1905_ = lean_unbox(v_fixed_1903_);
v_res_1906_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1901_, v_ver_1902_, v_fixed_boxed_1905_, v_self_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_1911_, size_t v_i_1912_, size_t v_stop_1913_, lean_object* v_b_1914_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_eq(v_i_1912_, v_stop_1913_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v_src_1917_; lean_object* v_ver_1918_; uint8_t v_fixed_1919_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1935_; 
v___x_1916_ = lean_array_uget_borrowed(v_as_1911_, v_i_1912_);
v_src_1917_ = lean_ctor_get(v___x_1916_, 0);
v_ver_1918_ = lean_ctor_get(v___x_1916_, 1);
v_fixed_1919_ = lean_ctor_get_uint8(v___x_1916_, sizeof(void*)*2);
if (v_fixed_1919_ == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1935_ = v___x_1939_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1940_; 
v___x_1940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1935_ = v___x_1940_;
goto v___jp_1934_;
}
v___jp_1920_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; 
v___x_1924_ = lean_string_append(v___y_1922_, v___y_1923_);
lean_dec_ref(v___y_1923_);
v___x_1925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1926_ = lean_string_append(v___x_1924_, v___x_1925_);
v___x_1927_ = 1;
lean_inc(v_src_1917_);
v___x_1928_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1917_, v___x_1927_);
v___x_1929_ = lean_string_append(v___x_1926_, v___x_1928_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_string_append(v___x_1929_, v___y_1921_);
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_add(v_i_1912_, v___x_1931_);
v_i_1912_ = v___x_1932_;
v_b_1914_ = v___x_1930_;
goto _start;
}
v___jp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_toString_1938_; 
v___x_1936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1937_ = lean_string_append(v_b_1914_, v___x_1936_);
v_toString_1938_ = lean_ctor_get(v_ver_1918_, 0);
lean_inc_ref(v_toString_1938_);
v___y_1921_ = v___y_1935_;
v___y_1922_ = v___x_1937_;
v___y_1923_ = v_toString_1938_;
goto v___jp_1920_;
}
}
else
{
return v_b_1914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_1941_, lean_object* v_i_1942_, lean_object* v_stop_1943_, lean_object* v_b_1944_){
_start:
{
size_t v_i_boxed_1945_; size_t v_stop_boxed_1946_; lean_object* v_res_1947_; 
v_i_boxed_1945_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_stop_boxed_1946_ = lean_unbox_usize(v_stop_1943_);
lean_dec(v_stop_1943_);
v_res_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1941_, v_i_boxed_1945_, v_stop_boxed_1946_, v_b_1944_);
lean_dec_ref(v_as_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_1948_, size_t v_i_1949_, size_t v_stop_1950_, lean_object* v_b_1951_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_usize_dec_eq(v_i_1949_, v_stop_1950_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v_src_1954_; lean_object* v_ver_1955_; uint8_t v_fixed_1956_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1972_; 
v___x_1953_ = lean_array_uget_borrowed(v_as_1948_, v_i_1949_);
v_src_1954_ = lean_ctor_get(v___x_1953_, 0);
v_ver_1955_ = lean_ctor_get(v___x_1953_, 1);
v_fixed_1956_ = lean_ctor_get_uint8(v___x_1953_, sizeof(void*)*2);
if (v_fixed_1956_ == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1972_ = v___x_1976_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1972_ = v___x_1977_;
goto v___jp_1971_;
}
v___jp_1957_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1961_ = lean_string_append(v___y_1959_, v___y_1960_);
lean_dec_ref(v___y_1960_);
v___x_1962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1963_ = lean_string_append(v___x_1961_, v___x_1962_);
v___x_1964_ = 1;
lean_inc(v_src_1954_);
v___x_1965_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1954_, v___x_1964_);
v___x_1966_ = lean_string_append(v___x_1963_, v___x_1965_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = lean_string_append(v___x_1966_, v___y_1958_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1949_, v___x_1968_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1948_, v___x_1969_, v_stop_1950_, v___x_1967_);
return v___x_1970_;
}
v___jp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_toString_1975_; 
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1974_ = lean_string_append(v_b_1951_, v___x_1973_);
v_toString_1975_ = lean_ctor_get(v_ver_1955_, 0);
lean_inc_ref(v_toString_1975_);
v___y_1958_ = v___y_1972_;
v___y_1959_ = v___x_1974_;
v___y_1960_ = v_toString_1975_;
goto v___jp_1957_;
}
}
else
{
return v_b_1951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_1978_, lean_object* v_i_1979_, lean_object* v_stop_1980_, lean_object* v_b_1981_){
_start:
{
size_t v_i_boxed_1982_; size_t v_stop_boxed_1983_; lean_object* v_res_1984_; 
v_i_boxed_1982_ = lean_unbox_usize(v_i_1979_);
lean_dec(v_i_1979_);
v_stop_boxed_1983_ = lean_unbox_usize(v_stop_1980_);
lean_dec(v_stop_1980_);
v_res_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_1978_, v_i_boxed_1982_, v_stop_boxed_1983_, v_b_1981_);
lean_dec_ref(v_as_1978_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_1985_, lean_object* v_as_1986_, size_t v_i_1987_, size_t v_stop_1988_, lean_object* v_b_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_eq(v_i_1987_, v_stop_1988_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v_relPkgDir_1994_; lean_object* v_manifestEntry_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1993_ = lean_array_uget_borrowed(v_as_1986_, v_i_1987_);
v_relPkgDir_1994_ = lean_ctor_get(v___x_1993_, 1);
v_manifestEntry_1995_ = lean_ctor_get(v___x_1993_, 4);
lean_inc_ref(v_relPkgDir_1994_);
lean_inc_ref(v___x_1985_);
v___x_1996_ = l_Lake_joinRelative(v___x_1985_, v_relPkgDir_1994_);
v___x_1997_ = l_Lake_toolchainFileName;
v___x_1998_ = l_System_FilePath_join(v___x_1996_, v___x_1997_);
v___x_1999_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1998_);
lean_dec_ref(v___x_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_a_2002_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1999_);
if (lean_obj_tag(v_a_2000_) == 1)
{
lean_object* v_tc_x3f_2006_; 
v_tc_x3f_2006_ = lean_ctor_get(v_b_1989_, 1);
if (lean_obj_tag(v_tc_x3f_2006_) == 1)
{
lean_object* v_val_2007_; lean_object* v_src_2008_; lean_object* v_clashes_2009_; uint8_t v_fixed_2010_; lean_object* v_val_2011_; uint8_t v___x_2012_; 
v_val_2007_ = lean_ctor_get(v_a_2000_, 0);
v_src_2008_ = lean_ctor_get(v_b_1989_, 0);
v_clashes_2009_ = lean_ctor_get(v_b_1989_, 2);
v_fixed_2010_ = lean_ctor_get_uint8(v_b_1989_, sizeof(void*)*3);
v_val_2011_ = lean_ctor_get(v_tc_x3f_2006_, 0);
v___x_2012_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1993_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lake_ToolchainVer_ble(v_val_2007_, v_val_2011_);
if (v___x_2022_ == 0)
{
lean_inc_ref(v_clashes_2009_);
lean_inc(v_src_2008_);
lean_inc_ref(v_tc_x3f_2006_);
lean_dec_ref(v_b_1989_);
if (v_fixed_2010_ == 0)
{
goto v___jp_2018_;
}
else
{
if (v___x_2012_ == 0)
{
lean_inc(v_val_2007_);
lean_dec_ref(v_a_2000_);
goto v___jp_2013_;
}
else
{
goto v___jp_2018_;
}
}
}
else
{
lean_dec_ref(v_a_2000_);
v_a_2002_ = v_b_1989_;
goto v___jp_2001_;
}
}
else
{
if (v_fixed_2010_ == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2037_; 
lean_inc_ref(v_clashes_2009_);
lean_inc(v_src_2008_);
lean_inc_ref(v_tc_x3f_2006_);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_b_1989_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2038_ = lean_ctor_get(v_b_1989_, 2);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_b_1989_, 1);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_b_1989_, 0);
lean_dec(v_unused_2040_);
v___x_2024_ = v_b_1989_;
v_isShared_2025_ = v_isSharedCheck_2037_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v_b_1989_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2037_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lake_ToolchainVer_ble(v_val_2011_, v_val_2007_);
if (v___x_2026_ == 0)
{
lean_object* v_name_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_inc(v_val_2007_);
lean_dec_ref(v_a_2000_);
v_name_2027_ = lean_ctor_get(v_manifestEntry_1995_, 0);
lean_inc(v_name_2027_);
v___x_2028_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2028_, 0, v_name_2027_);
lean_ctor_set(v___x_2028_, 1, v_val_2007_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*2, v___x_2012_);
v___x_2029_ = lean_array_push(v_clashes_2009_, v___x_2028_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 2, v___x_2029_);
v___x_2031_ = v___x_2024_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_src_2008_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_tc_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v___x_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2032_, sizeof(void*)*3, v_fixed_2010_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v_a_2002_ = v___x_2031_;
goto v___jp_2001_;
}
}
else
{
lean_object* v_name_2033_; lean_object* v___x_2035_; 
lean_dec(v_src_2008_);
lean_dec_ref(v_tc_x3f_2006_);
v_name_2033_ = lean_ctor_get(v_manifestEntry_1995_, 0);
lean_inc(v_name_2033_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_a_2000_);
lean_ctor_set(v___x_2024_, 0, v_name_2033_);
v___x_2035_ = v___x_2024_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_name_2033_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_a_2000_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_clashes_2009_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_ctor_set_uint8(v___x_2035_, sizeof(void*)*3, v___x_2012_);
v_a_2002_ = v___x_2035_;
goto v___jp_2001_;
}
}
}
}
else
{
uint8_t v___x_2041_; 
lean_inc_n(v_val_2007_, 2);
lean_dec_ref(v_a_2000_);
lean_inc(v_val_2011_);
v___x_2041_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2011_, v_val_2007_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2051_; 
lean_inc_ref(v_clashes_2009_);
lean_inc(v_src_2008_);
lean_inc_ref(v_tc_x3f_2006_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_b_1989_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; lean_object* v_unused_2054_; 
v_unused_2052_ = lean_ctor_get(v_b_1989_, 2);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_b_1989_, 1);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_b_1989_, 0);
lean_dec(v_unused_2054_);
v___x_2043_ = v_b_1989_;
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_b_1989_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_name_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v_name_2045_ = lean_ctor_get(v_manifestEntry_1995_, 0);
lean_inc(v_name_2045_);
v___x_2046_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2046_, 0, v_name_2045_);
lean_ctor_set(v___x_2046_, 1, v_val_2007_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*2, v___x_2012_);
v___x_2047_ = lean_array_push(v_clashes_2009_, v___x_2046_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v___x_2047_);
v___x_2049_ = v___x_2043_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_src_2008_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_tc_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v___x_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*3, v_fixed_2010_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
v_a_2002_ = v___x_2049_;
goto v___jp_2001_;
}
}
}
else
{
lean_dec(v_val_2007_);
v_a_2002_ = v_b_1989_;
goto v___jp_2001_;
}
}
}
v___jp_2013_:
{
lean_object* v_name_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_name_2014_ = lean_ctor_get(v_manifestEntry_1995_, 0);
lean_inc(v_name_2014_);
v___x_2015_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2015_, 0, v_name_2014_);
lean_ctor_set(v___x_2015_, 1, v_val_2007_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2, v___x_2012_);
v___x_2016_ = lean_array_push(v_clashes_2009_, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2017_, 0, v_src_2008_);
lean_ctor_set(v___x_2017_, 1, v_tc_x3f_2006_);
lean_ctor_set(v___x_2017_, 2, v___x_2016_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*3, v_fixed_2010_);
v_a_2002_ = v___x_2017_;
goto v___jp_2001_;
}
v___jp_2018_:
{
uint8_t v___x_2019_; 
v___x_2019_ = l_Lake_ToolchainVer_blt(v_val_2011_, v_val_2007_);
if (v___x_2019_ == 0)
{
lean_inc(v_val_2007_);
lean_dec_ref(v_a_2000_);
goto v___jp_2013_;
}
else
{
lean_object* v_name_2020_; lean_object* v___x_2021_; 
lean_dec(v_src_2008_);
lean_dec_ref(v_tc_x3f_2006_);
v_name_2020_ = lean_ctor_get(v_manifestEntry_1995_, 0);
lean_inc(v_name_2020_);
v___x_2021_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2021_, 0, v_name_2020_);
lean_ctor_set(v___x_2021_, 1, v_a_2000_);
lean_ctor_set(v___x_2021_, 2, v_clashes_2009_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3, v___x_2012_);
v_a_2002_ = v___x_2021_;
goto v___jp_2001_;
}
}
}
else
{
lean_object* v_clashes_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2064_; 
v_clashes_2055_ = lean_ctor_get(v_b_1989_, 2);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_b_1989_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; 
v_unused_2065_ = lean_ctor_get(v_b_1989_, 1);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_b_1989_, 0);
lean_dec(v_unused_2066_);
v___x_2057_ = v_b_1989_;
v_isShared_2058_ = v_isSharedCheck_2064_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_clashes_2055_);
lean_dec(v_b_1989_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2064_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_name_2059_; uint8_t v___x_2060_; lean_object* v___x_2062_; 
v_name_2059_ = lean_ctor_get(v_manifestEntry_1995_, 0);
v___x_2060_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1993_);
lean_inc(v_name_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_a_2000_);
lean_ctor_set(v___x_2057_, 0, v_name_2059_);
v___x_2062_ = v___x_2057_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_name_2059_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_a_2000_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_clashes_2055_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*3, v___x_2060_);
v_a_2002_ = v___x_2062_;
goto v___jp_2001_;
}
}
}
}
else
{
lean_dec(v_a_2000_);
v_a_2002_ = v_b_1989_;
goto v___jp_2001_;
}
v___jp_2001_:
{
size_t v___x_2003_; size_t v___x_2004_; 
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_add(v_i_1987_, v___x_2003_);
v_i_1987_ = v___x_2004_;
v_b_1989_ = v_a_2002_;
goto _start;
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_b_1989_);
lean_dec_ref(v___x_1985_);
v_a_2067_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2069_ = v___x_1999_;
v_isShared_2070_ = v_isSharedCheck_2079_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1999_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2079_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2071_ = lean_io_error_to_string(v_a_2067_);
v___x_2072_ = 3;
v___x_2073_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*1, v___x_2072_);
lean_inc_ref(v___y_1990_);
v___x_2074_ = lean_apply_2(v___y_1990_, v___x_2073_, lean_box(0));
v___x_2075_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2075_);
v___x_2077_ = v___x_2069_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2080_; 
lean_dec_ref(v___x_1985_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v_b_1989_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2081_, lean_object* v_as_2082_, lean_object* v_i_2083_, lean_object* v_stop_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
size_t v_i_boxed_2088_; size_t v_stop_boxed_2089_; lean_object* v_res_2090_; 
v_i_boxed_2088_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_stop_boxed_2089_ = lean_unbox_usize(v_stop_2084_);
lean_dec(v_stop_2084_);
v_res_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2081_, v_as_2082_, v_i_boxed_2088_, v_stop_boxed_2089_, v_b_2085_, v___y_2086_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v_as_2082_);
return v_res_2090_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2100_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_2101_ = lean_unsigned_to_nat(4u);
v___x_2102_ = lean_mk_empty_array_with_capacity(v___x_2101_);
v___x_2103_ = lean_array_push(v___x_2102_, v___x_2100_);
return v___x_2103_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2105_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_2106_ = lean_array_push(v___x_2105_, v___x_2104_);
return v___x_2106_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = 4;
v___x_2112_ = lean_uint32_to_uint8(v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2130_, lean_object* v_rootDeps_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___y_2135_; lean_object* v_lakeEnv_2140_; lean_object* v_lakeArgs_x3f_2141_; lean_object* v_packages_2142_; lean_object* v___y_2144_; uint8_t v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2289_; lean_object* v___y_2290_; uint8_t v___y_2291_; lean_object* v___x_2294_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2308_; lean_object* v___y_2309_; uint8_t v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___x_2330_; lean_object* v_baseName_2331_; lean_object* v_dir_2332_; lean_object* v_config_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_lakeEnv_2140_ = lean_ctor_get(v_ws_2130_, 0);
lean_inc_ref(v_lakeEnv_2140_);
v_lakeArgs_x3f_2141_ = lean_ctor_get(v_ws_2130_, 3);
lean_inc(v_lakeArgs_x3f_2141_);
v_packages_2142_ = lean_ctor_get(v_ws_2130_, 4);
lean_inc_ref(v_packages_2142_);
lean_dec_ref(v_ws_2130_);
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_array_fget(v_packages_2142_, v___x_2294_);
lean_dec_ref(v_packages_2142_);
v_baseName_2331_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_baseName_2331_);
v_dir_2332_ = lean_ctor_get(v___x_2330_, 4);
lean_inc_ref_n(v_dir_2332_, 2);
v_config_2333_ = lean_ctor_get(v___x_2330_, 6);
lean_inc_ref(v_config_2333_);
lean_dec(v___x_2330_);
v___x_2334_ = l_Lake_toolchainFileName;
v___x_2335_ = l_System_FilePath_join(v_dir_2332_, v___x_2334_);
v___x_2336_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2335_);
lean_dec_ref(v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2395_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2395_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2395_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_src_2342_; lean_object* v_tc_x3f_2343_; lean_object* v_clashes_2344_; uint8_t v_fixed_2345_; lean_object* v___y_2369_; uint8_t v_fixedToolchain_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_fixedToolchain_2383_ = lean_ctor_get_uint8(v_config_2333_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_2333_);
v___x_2384_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2385_ = lean_array_get_size(v_rootDeps_2131_);
v___x_2386_ = lean_nat_dec_lt(v___x_2294_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_inc(v_a_2337_);
v_src_2342_ = v_baseName_2331_;
v_tc_x3f_2343_ = v_a_2337_;
v_clashes_2344_ = v___x_2384_;
v_fixed_2345_ = v_fixedToolchain_2383_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
lean_inc(v_a_2337_);
lean_inc(v_baseName_2331_);
v___x_2387_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2387_, 0, v_baseName_2331_);
lean_ctor_set(v___x_2387_, 1, v_a_2337_);
lean_ctor_set(v___x_2387_, 2, v___x_2384_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*3, v_fixedToolchain_2383_);
v___x_2388_ = lean_nat_dec_le(v___x_2385_, v___x_2385_);
if (v___x_2388_ == 0)
{
if (v___x_2386_ == 0)
{
lean_dec_ref(v___x_2387_);
lean_inc(v_a_2337_);
v_src_2342_ = v_baseName_2331_;
v_tc_x3f_2343_ = v_a_2337_;
v_clashes_2344_ = v___x_2384_;
v_fixed_2345_ = v_fixedToolchain_2383_;
goto v___jp_2341_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v_baseName_2331_);
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = lean_usize_of_nat(v___x_2385_);
lean_inc_ref(v_dir_2332_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2332_, v_rootDeps_2131_, v___x_2389_, v___x_2390_, v___x_2387_, v_a_2132_);
v___y_2369_ = v___x_2391_;
goto v___jp_2368_;
}
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_baseName_2331_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = lean_usize_of_nat(v___x_2385_);
lean_inc_ref(v_dir_2332_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2332_, v_rootDeps_2131_, v___x_2392_, v___x_2393_, v___x_2387_, v_a_2132_);
v___y_2369_ = v___x_2394_;
goto v___jp_2368_;
}
}
v___jp_2341_:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_array_get_size(v_clashes_2344_);
v___x_2347_ = lean_nat_dec_lt(v___x_2294_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_dec_ref(v_clashes_2344_);
lean_dec(v_src_2342_);
if (lean_obj_tag(v_tc_x3f_2343_) == 1)
{
lean_object* v_val_2348_; lean_object* v_rootToolchainFile_2349_; 
v_val_2348_ = lean_ctor_get(v_tc_x3f_2343_, 0);
lean_inc(v_val_2348_);
lean_dec_ref(v_tc_x3f_2343_);
v_rootToolchainFile_2349_ = l_Lake_joinRelative(v_dir_2332_, v___x_2334_);
if (lean_obj_tag(v_a_2337_) == 0)
{
lean_del_object(v___x_2339_);
v___y_2289_ = v_rootToolchainFile_2349_;
v___y_2290_ = v_val_2348_;
v___y_2291_ = v___x_2347_;
goto v___jp_2288_;
}
else
{
lean_object* v_val_2350_; uint8_t v___x_2351_; 
v_val_2350_ = lean_ctor_get(v_a_2337_, 0);
lean_inc(v_val_2350_);
lean_dec_ref(v_a_2337_);
lean_inc(v_val_2348_);
v___x_2351_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2350_, v_val_2348_);
if (v___x_2351_ == 0)
{
lean_del_object(v___x_2339_);
v___y_2289_ = v_rootToolchainFile_2349_;
v___y_2290_ = v_val_2348_;
v___y_2291_ = v___x_2351_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec_ref(v_rootToolchainFile_2349_);
lean_dec(v_val_2348_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
v___x_2352_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2132_);
v___x_2353_ = lean_apply_2(v_a_2132_, v___x_2352_, lean_box(0));
v___x_2354_ = lean_box(0);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2354_);
v___x_2356_ = v___x_2339_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_dec(v_tc_x3f_2343_);
lean_dec(v_a_2337_);
lean_dec_ref(v_dir_2332_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
v___x_2358_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2132_);
v___x_2359_ = lean_apply_2(v_a_2132_, v___x_2358_, lean_box(0));
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2359_);
v___x_2361_ = v___x_2339_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_del_object(v___x_2339_);
lean_dec(v_a_2337_);
lean_dec_ref(v_dir_2332_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
if (lean_obj_tag(v_tc_x3f_2343_) == 1)
{
if (v_fixed_2345_ == 0)
{
lean_object* v_val_2363_; lean_object* v___x_2364_; 
v_val_2363_ = lean_ctor_get(v_tc_x3f_2343_, 0);
lean_inc(v_val_2363_);
lean_dec_ref(v_tc_x3f_2343_);
v___x_2364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2322_ = v_src_2342_;
v___y_2323_ = v___x_2347_;
v___y_2324_ = v___x_2346_;
v___y_2325_ = v_clashes_2344_;
v___y_2326_ = v_val_2363_;
v___y_2327_ = v___x_2364_;
goto v___jp_2321_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2366_; 
v_val_2365_ = lean_ctor_get(v_tc_x3f_2343_, 0);
lean_inc(v_val_2365_);
lean_dec_ref(v_tc_x3f_2343_);
v___x_2366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2322_ = v_src_2342_;
v___y_2323_ = v___x_2347_;
v___y_2324_ = v___x_2346_;
v___y_2325_ = v_clashes_2344_;
v___y_2326_ = v_val_2365_;
v___y_2327_ = v___x_2366_;
goto v___jp_2321_;
}
}
else
{
lean_object* v___x_2367_; 
lean_dec(v_tc_x3f_2343_);
lean_dec(v_src_2342_);
v___x_2367_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2296_ = v___x_2346_;
v___y_2297_ = v_clashes_2344_;
v___y_2298_ = v___x_2367_;
goto v___jp_2295_;
}
}
}
v___jp_2368_:
{
if (lean_obj_tag(v___y_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v_src_2371_; lean_object* v_tc_x3f_2372_; lean_object* v_clashes_2373_; uint8_t v_fixed_2374_; 
v_a_2370_ = lean_ctor_get(v___y_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___y_2369_);
v_src_2371_ = lean_ctor_get(v_a_2370_, 0);
lean_inc(v_src_2371_);
v_tc_x3f_2372_ = lean_ctor_get(v_a_2370_, 1);
lean_inc(v_tc_x3f_2372_);
v_clashes_2373_ = lean_ctor_get(v_a_2370_, 2);
lean_inc_ref(v_clashes_2373_);
v_fixed_2374_ = lean_ctor_get_uint8(v_a_2370_, sizeof(void*)*3);
lean_dec(v_a_2370_);
v_src_2342_ = v_src_2371_;
v_tc_x3f_2343_ = v_tc_x3f_2372_;
v_clashes_2344_ = v_clashes_2373_;
v_fixed_2345_ = v_fixed_2374_;
goto v___jp_2341_;
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_del_object(v___x_2339_);
lean_dec(v_a_2337_);
lean_dec_ref(v_dir_2332_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
v_a_2375_ = lean_ctor_get(v___y_2369_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___y_2369_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___y_2369_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___y_2369_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_config_2333_);
lean_dec_ref(v_dir_2332_);
lean_dec(v_baseName_2331_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
v_a_2396_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2398_ = v___x_2336_;
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2336_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2400_ = lean_io_error_to_string(v_a_2396_);
v___x_2401_ = 3;
v___x_2402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*1, v___x_2401_);
lean_inc_ref(v_a_2132_);
v___x_2403_ = lean_apply_2(v_a_2132_, v___x_2402_, lean_box(0));
v___x_2404_ = lean_box(0);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2404_);
v___x_2406_ = v___x_2398_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
v___jp_2134_:
{
uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2136_ = 2;
v___x_2137_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2137_, 0, v___y_2135_);
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*1, v___x_2136_);
lean_inc_ref(v_a_2132_);
v___x_2138_ = lean_apply_2(v_a_2132_, v___x_2137_, lean_box(0));
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
v___jp_2143_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_inc_ref(v___y_2146_);
v___x_2148_ = lean_string_append(v___y_2146_, v___y_2147_);
v___x_2149_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2150_ = lean_string_append(v___x_2148_, v___x_2149_);
v___x_2151_ = 1;
v___x_2152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*1, v___x_2151_);
lean_inc_ref(v_a_2132_);
v___x_2153_ = lean_apply_2(v_a_2132_, v___x_2152_, lean_box(0));
v___x_2154_ = l_IO_FS_writeFile(v___y_2144_, v___y_2147_);
lean_dec_ref(v___y_2144_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_dec_ref(v___x_2154_);
if (lean_obj_tag(v_lakeArgs_x3f_2141_) == 1)
{
lean_object* v_elan_x3f_2155_; 
v_elan_x3f_2155_ = lean_ctor_get(v_lakeEnv_2140_, 2);
if (lean_obj_tag(v_elan_x3f_2155_) == 1)
{
lean_object* v_val_2156_; lean_object* v_val_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_elan_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_val_2156_ = lean_ctor_get(v_lakeArgs_x3f_2141_, 0);
lean_inc(v_val_2156_);
lean_dec_ref(v_lakeArgs_x3f_2141_);
v_val_2157_ = lean_ctor_get(v_elan_x3f_2155_, 0);
v___x_2158_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2132_);
v___x_2159_ = lean_apply_2(v_a_2132_, v___x_2158_, lean_box(0));
v___x_2160_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2161_ = lean_ctor_get(v_val_2157_, 1);
lean_inc_ref(v_elan_2161_);
v___x_2162_ = 1;
v___x_2163_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2164_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2165_ = lean_array_push(v___x_2164_, v___y_2147_);
v___x_2166_ = lean_array_push(v___x_2165_, v___x_2163_);
v___x_2167_ = l_Array_append___redArg(v___x_2166_, v_val_2156_);
lean_dec(v_val_2156_);
v___x_2168_ = lean_box(0);
v___x_2169_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2140_);
v___x_2170_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2170_, 0, v___x_2160_);
lean_ctor_set(v___x_2170_, 1, v_elan_2161_);
lean_ctor_set(v___x_2170_, 2, v___x_2167_);
lean_ctor_set(v___x_2170_, 3, v___x_2168_);
lean_ctor_set(v___x_2170_, 4, v___x_2169_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*5, v___x_2162_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*5 + 1, v___y_2145_);
v___x_2171_ = lean_io_process_spawn(v___x_2170_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = lean_io_process_child_wait(v___x_2160_, v_a_2172_);
lean_dec(v_a_2172_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; uint32_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = lean_unbox_uint32(v_a_2174_);
lean_dec(v_a_2174_);
v___x_2176_ = lean_uint32_to_uint8(v___x_2175_);
v___x_2177_ = lean_io_exit(v___x_2176_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2198_; 
v_a_2186_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2190_ = lean_io_error_to_string(v_a_2186_);
v___x_2191_ = 3;
v___x_2192_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*1, v___x_2191_);
lean_inc_ref(v_a_2132_);
v___x_2193_ = lean_apply_2(v_a_2132_, v___x_2192_, lean_box(0));
v___x_2194_ = lean_box(0);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2194_);
v___x_2196_ = v___x_2188_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2211_; 
v_a_2199_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2201_ = v___x_2173_;
v_isShared_2202_ = v_isSharedCheck_2211_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2173_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2211_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2203_ = lean_io_error_to_string(v_a_2199_);
v___x_2204_ = 3;
v___x_2205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*1, v___x_2204_);
lean_inc_ref(v_a_2132_);
v___x_2206_ = lean_apply_2(v_a_2132_, v___x_2205_, lean_box(0));
v___x_2207_ = lean_box(0);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2207_);
v___x_2209_ = v___x_2201_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2224_; 
v_a_2212_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2214_ = v___x_2171_;
v_isShared_2215_ = v_isSharedCheck_2224_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2171_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2224_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2216_ = lean_io_error_to_string(v_a_2212_);
v___x_2217_ = 3;
v___x_2218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*1, v___x_2217_);
lean_inc_ref(v_a_2132_);
v___x_2219_ = lean_apply_2(v_a_2132_, v___x_2218_, lean_box(0));
v___x_2220_ = lean_box(0);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2220_);
v___x_2222_ = v___x_2214_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_lakeArgs_x3f_2141_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_lakeEnv_2140_);
v___x_2225_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2132_);
v___x_2226_ = lean_apply_2(v_a_2132_, v___x_2225_, lean_box(0));
v___x_2227_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2228_ = lean_io_exit(v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2249_; 
v_a_2237_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2239_ = v___x_2228_;
v_isShared_2240_ = v_isSharedCheck_2249_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2228_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2249_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2241_ = lean_io_error_to_string(v_a_2237_);
v___x_2242_ = 3;
v___x_2243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*1, v___x_2242_);
lean_inc_ref(v_a_2132_);
v___x_2244_ = lean_apply_2(v_a_2132_, v___x_2243_, lean_box(0));
v___x_2245_ = lean_box(0);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2245_);
v___x_2247_ = v___x_2239_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref(v___y_2147_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
v___x_2250_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2132_);
v___x_2251_ = lean_apply_2(v_a_2132_, v___x_2250_, lean_box(0));
v___x_2252_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2253_ = lean_io_exit(v___x_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2274_; 
v_a_2262_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2264_ = v___x_2253_;
v_isShared_2265_ = v_isSharedCheck_2274_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2253_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2274_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2266_ = lean_io_error_to_string(v_a_2262_);
v___x_2267_ = 3;
v___x_2268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set_uint8(v___x_2268_, sizeof(void*)*1, v___x_2267_);
lean_inc_ref(v_a_2132_);
v___x_2269_ = lean_apply_2(v_a_2132_, v___x_2268_, lean_box(0));
v___x_2270_ = lean_box(0);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2270_);
v___x_2272_ = v___x_2264_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v___y_2147_);
lean_dec(v_lakeArgs_x3f_2141_);
lean_dec_ref(v_lakeEnv_2140_);
v_a_2275_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2277_ = v___x_2154_;
v_isShared_2278_ = v_isSharedCheck_2287_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2154_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2287_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2279_ = lean_io_error_to_string(v_a_2275_);
v___x_2280_ = 3;
v___x_2281_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*1, v___x_2280_);
lean_inc_ref(v_a_2132_);
v___x_2282_ = lean_apply_2(v_a_2132_, v___x_2281_, lean_box(0));
v___x_2283_ = lean_box(0);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2283_);
v___x_2285_ = v___x_2277_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
v___jp_2288_:
{
lean_object* v___x_2292_; lean_object* v_toString_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2293_ = lean_ctor_get(v___y_2290_, 0);
lean_inc_ref(v_toString_2293_);
lean_dec_ref(v___y_2290_);
v___y_2144_ = v___y_2289_;
v___y_2145_ = v___y_2291_;
v___y_2146_ = v___x_2292_;
v___y_2147_ = v_toString_2293_;
goto v___jp_2143_;
}
v___jp_2295_:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_nat_dec_lt(v___x_2294_, v___y_2296_);
if (v___x_2299_ == 0)
{
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
v___y_2135_ = v___y_2298_;
goto v___jp_2134_;
}
else
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_nat_dec_le(v___y_2296_, v___y_2296_);
if (v___x_2300_ == 0)
{
if (v___x_2299_ == 0)
{
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
v___y_2135_ = v___y_2298_;
goto v___jp_2134_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = lean_usize_of_nat(v___y_2296_);
lean_dec(v___y_2296_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2297_, v___x_2301_, v___x_2302_, v___y_2298_);
lean_dec_ref(v___y_2297_);
v___y_2135_ = v___x_2303_;
goto v___jp_2134_;
}
}
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = ((size_t)0ULL);
v___x_2305_ = lean_usize_of_nat(v___y_2296_);
lean_dec(v___y_2296_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2297_, v___x_2304_, v___x_2305_, v___y_2298_);
lean_dec_ref(v___y_2297_);
v___y_2135_ = v___x_2306_;
goto v___jp_2134_;
}
}
}
v___jp_2307_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_inc_ref(v___y_2313_);
v___x_2315_ = lean_string_append(v___y_2313_, v___y_2314_);
lean_dec_ref(v___y_2314_);
v___x_2316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2317_ = lean_string_append(v___x_2315_, v___x_2316_);
v___x_2318_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2311_, v___y_2310_);
v___x_2319_ = lean_string_append(v___x_2317_, v___x_2318_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = lean_string_append(v___x_2319_, v___y_2308_);
v___y_2296_ = v___y_2309_;
v___y_2297_ = v___y_2312_;
v___y_2298_ = v___x_2320_;
goto v___jp_2295_;
}
v___jp_2321_:
{
lean_object* v___x_2328_; lean_object* v_toString_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2329_ = lean_ctor_get(v___y_2326_, 0);
lean_inc_ref(v_toString_2329_);
lean_dec_ref(v___y_2326_);
v___y_2308_ = v___y_2327_;
v___y_2309_ = v___y_2324_;
v___y_2310_ = v___y_2323_;
v___y_2311_ = v___y_2322_;
v___y_2312_ = v___y_2325_;
v___y_2313_ = v___x_2328_;
v___y_2314_ = v_toString_2329_;
goto v___jp_2307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2409_, lean_object* v_rootDeps_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2409_, v_rootDeps_2410_, v_a_2411_);
lean_dec_ref(v_a_2411_);
lean_dec_ref(v_rootDeps_2410_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2414_, lean_object* v_dep_2415_, lean_object* v_ws_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2416_, v_pkg_2414_, v_dep_2415_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v_fst_2422_; lean_object* v_snd_2423_; lean_object* v___x_2424_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
v_fst_2422_ = lean_ctor_get(v_a_2421_, 0);
lean_inc_n(v_fst_2422_, 2);
v_snd_2423_ = lean_ctor_get(v_a_2421_, 1);
lean_inc(v_snd_2423_);
lean_dec(v_a_2421_);
v___x_2424_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2422_, v_snd_2423_, v_a_2418_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2441_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2441_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2441_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_snd_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2439_; 
v_snd_2429_ = lean_ctor_get(v_a_2425_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v_a_2425_, 0);
lean_dec(v_unused_2440_);
v___x_2431_ = v_a_2425_;
v_isShared_2432_ = v_isSharedCheck_2439_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snd_2429_);
lean_dec(v_a_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2439_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v_fst_2422_);
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_fst_2422_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_snd_2429_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2434_);
v___x_2436_ = v___x_2427_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_fst_2422_);
v_a_2442_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2424_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2424_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2450_, lean_object* v_dep_2451_, lean_object* v_ws_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2450_, v_dep_2451_, v_ws_2452_, v_a_2453_, v_a_2454_);
lean_dec_ref(v_a_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2457_, lean_object* v_ws_2458_, lean_object* v_pkg_2459_, lean_object* v_dep_2460_, lean_object* v_a_2461_){
_start:
{
uint8_t v___y_2464_; lean_object* v___y_2465_; lean_object* v_name_2495_; lean_object* v___x_2496_; 
v_name_2495_ = lean_ctor_get(v_dep_2460_, 0);
v___x_2496_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2461_, v_name_2495_);
if (lean_obj_tag(v___x_2496_) == 1)
{
lean_object* v_val_2497_; lean_object* v_lakeEnv_2498_; lean_object* v_packages_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v_config_2502_; lean_object* v_dir_2503_; lean_object* v_toWorkspaceConfig_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_dep_2460_);
lean_dec_ref(v_pkg_2459_);
v_val_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2497_);
lean_dec_ref(v___x_2496_);
v_lakeEnv_2498_ = lean_ctor_get(v_ws_2458_, 0);
lean_inc_ref(v_lakeEnv_2498_);
v_packages_2499_ = lean_ctor_get(v_ws_2458_, 4);
lean_inc_ref(v_packages_2499_);
lean_dec_ref(v_ws_2458_);
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_array_fget(v_packages_2499_, v___x_2500_);
lean_dec_ref(v_packages_2499_);
v_config_2502_ = lean_ctor_get(v___x_2501_, 6);
lean_inc_ref(v_config_2502_);
v_dir_2503_ = lean_ctor_get(v___x_2501_, 4);
lean_inc_ref(v_dir_2503_);
lean_dec(v___x_2501_);
v_toWorkspaceConfig_2504_ = lean_ctor_get(v_config_2502_, 0);
lean_inc_ref(v_toWorkspaceConfig_2504_);
lean_dec_ref(v_config_2502_);
v___x_2505_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2504_);
v___x_2506_ = l_Lake_PackageEntry_materialize(v_val_2497_, v_lakeEnv_2498_, v_dir_2503_, v___x_2505_, v___y_2457_);
lean_dec_ref(v_lakeEnv_2498_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2515_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2515_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2515_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_a_2507_);
lean_ctor_set(v___x_2511_, 1, v_a_2461_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2511_);
v___x_2513_ = v___x_2509_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2461_);
v_a_2516_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2506_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2506_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_wsIdx_2524_; lean_object* v_relDir_2525_; uint8_t v___y_2527_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
lean_dec(v___x_2496_);
v_wsIdx_2524_ = lean_ctor_get(v_pkg_2459_, 0);
lean_inc(v_wsIdx_2524_);
v_relDir_2525_ = lean_ctor_get(v_pkg_2459_, 5);
lean_inc_ref(v_relDir_2525_);
lean_dec_ref(v_pkg_2459_);
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_nat_dec_eq(v_wsIdx_2524_, v___x_2531_);
lean_dec(v_wsIdx_2524_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
v___x_2533_ = 1;
v___y_2527_ = v___x_2533_;
goto v___jp_2526_;
}
else
{
uint8_t v___x_2534_; 
v___x_2534_ = 0;
v___y_2527_ = v___x_2534_;
goto v___jp_2526_;
}
v___jp_2526_:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2529_ = lean_string_dec_eq(v_relDir_2525_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lake_joinRelative(v_relDir_2525_, v___x_2528_);
v___y_2464_ = v___y_2527_;
v___y_2465_ = v___x_2530_;
goto v___jp_2463_;
}
else
{
v___y_2464_ = v___y_2527_;
v___y_2465_ = v_relDir_2525_;
goto v___jp_2463_;
}
}
}
v___jp_2463_:
{
lean_object* v_lakeEnv_2466_; lean_object* v_packages_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_config_2470_; lean_object* v_dir_2471_; lean_object* v_toWorkspaceConfig_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_lakeEnv_2466_ = lean_ctor_get(v_ws_2458_, 0);
lean_inc_ref(v_lakeEnv_2466_);
v_packages_2467_ = lean_ctor_get(v_ws_2458_, 4);
lean_inc_ref(v_packages_2467_);
lean_dec_ref(v_ws_2458_);
v___x_2468_ = lean_unsigned_to_nat(0u);
v___x_2469_ = lean_array_fget(v_packages_2467_, v___x_2468_);
lean_dec_ref(v_packages_2467_);
v_config_2470_ = lean_ctor_get(v___x_2469_, 6);
lean_inc_ref(v_config_2470_);
v_dir_2471_ = lean_ctor_get(v___x_2469_, 4);
lean_inc_ref(v_dir_2471_);
lean_dec(v___x_2469_);
v_toWorkspaceConfig_2472_ = lean_ctor_get(v_config_2470_, 0);
lean_inc_ref(v_toWorkspaceConfig_2472_);
lean_dec_ref(v_config_2470_);
v___x_2473_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2472_);
v___x_2474_ = l_Lake_Dependency_materialize(v_dep_2460_, v___y_2464_, v_lakeEnv_2466_, v_dir_2471_, v___x_2473_, v___y_2465_, v___y_2457_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2486_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_manifestEntry_2479_; lean_object* v_name_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v_manifestEntry_2479_ = lean_ctor_get(v_a_2475_, 4);
v_name_2480_ = lean_ctor_get(v_manifestEntry_2479_, 0);
lean_inc_ref(v_manifestEntry_2479_);
lean_inc(v_name_2480_);
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2480_, v_manifestEntry_2479_, v_a_2461_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_a_2475_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2482_);
v___x_2484_ = v___x_2477_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2461_);
v_a_2487_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2474_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2474_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2535_, lean_object* v_ws_2536_, lean_object* v_pkg_2537_, lean_object* v_dep_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2535_, v_ws_2536_, v_pkg_2537_, v_dep_2538_, v_a_2539_);
lean_dec_ref(v___y_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2542_, lean_object* v_dep_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_manifestEntry_2546_; lean_object* v_pkgDir_2547_; lean_object* v_name_2548_; lean_object* v_manifestFile_x3f_2549_; lean_object* v___y_2551_; lean_object* v_fst_2552_; lean_object* v_snd_2553_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v_val_2613_; lean_object* v___y_2641_; 
v_manifestEntry_2546_ = lean_ctor_get(v_dep_2543_, 4);
v_pkgDir_2547_ = lean_ctor_get(v_dep_2543_, 0);
v_name_2548_ = lean_ctor_get(v_manifestEntry_2546_, 0);
v_manifestFile_x3f_2549_ = lean_ctor_get(v_manifestEntry_2546_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2549_) == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2547_);
v___x_2662_ = l_Lake_joinRelative(v_pkgDir_2547_, v___x_2661_);
v___y_2641_ = v___x_2662_;
goto v___jp_2640_;
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2664_; 
v_val_2663_ = lean_ctor_get(v_manifestFile_x3f_2549_, 0);
lean_inc(v_val_2663_);
lean_inc_ref(v_pkgDir_2547_);
v___x_2664_ = l_Lake_joinRelative(v_pkgDir_2547_, v_val_2663_);
v___y_2641_ = v___x_2664_;
goto v___jp_2640_;
}
v___jp_2550_:
{
if (lean_obj_tag(v_fst_2552_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2583_; 
lean_inc(v_name_2548_);
lean_dec_ref(v_dep_2543_);
v_a_2554_ = lean_ctor_get(v_fst_2552_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_fst_2552_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2556_ = v_fst_2552_;
v_isShared_2557_ = v_isSharedCheck_2583_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v_fst_2552_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2583_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
if (lean_obj_tag(v_a_2554_) == 11)
{
uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_dec_ref(v_a_2554_);
v___x_2558_ = 0;
v___x_2559_ = l_Lean_Name_toString(v_name_2548_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2561_ = lean_string_append(v___x_2559_, v___x_2560_);
v___x_2562_ = lean_string_append(v___x_2561_, v___y_2551_);
lean_dec_ref(v___y_2551_);
v___x_2563_ = 2;
v___x_2564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*1, v___x_2563_);
v___x_2565_ = lean_apply_2(v___y_2542_, v___x_2564_, lean_box(0));
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_snd_2553_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2566_);
v___x_2568_ = v___x_2556_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
else
{
uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
lean_dec_ref(v___y_2551_);
v___x_2570_ = 0;
v___x_2571_ = l_Lean_Name_toString(v_name_2548_, v___x_2570_);
v___x_2572_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2573_ = lean_string_append(v___x_2571_, v___x_2572_);
v___x_2574_ = lean_io_error_to_string(v_a_2554_);
v___x_2575_ = lean_string_append(v___x_2573_, v___x_2574_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = 2;
v___x_2577_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*1, v___x_2576_);
v___x_2578_ = lean_apply_2(v___y_2542_, v___x_2577_, lean_box(0));
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v_snd_2553_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2579_);
v___x_2581_ = v___x_2556_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v___y_2551_);
lean_dec_ref(v___y_2542_);
v_a_2584_ = lean_ctor_get(v_fst_2552_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_fst_2552_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2586_ = v_fst_2552_;
v_isShared_2587_ = v_isSharedCheck_2608_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v_fst_2552_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2608_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v_packages_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_packages_2588_ = lean_ctor_get(v_a_2584_, 3);
lean_inc_ref(v_packages_2588_);
lean_dec(v_a_2584_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_array_get_size(v_packages_2588_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_nat_dec_lt(v___x_2589_, v___x_2590_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec_ref(v_packages_2588_);
lean_dec_ref(v_dep_2543_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v_snd_2553_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set_tag(v___x_2586_, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2593_);
v___x_2595_ = v___x_2586_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_nat_dec_le(v___x_2590_, v___x_2590_);
if (v___x_2597_ == 0)
{
if (v___x_2592_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec_ref(v_packages_2588_);
lean_dec_ref(v_dep_2543_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2591_);
lean_ctor_set(v___x_2598_, 1, v_snd_2553_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set_tag(v___x_2586_, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2598_);
v___x_2600_ = v___x_2586_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
lean_del_object(v___x_2586_);
v___x_2602_ = ((size_t)0ULL);
v___x_2603_ = lean_usize_of_nat(v___x_2590_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2543_, v_packages_2588_, v___x_2602_, v___x_2603_, v___x_2591_, v_snd_2553_);
lean_dec_ref(v_packages_2588_);
return v___x_2604_;
}
}
else
{
size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; 
lean_del_object(v___x_2586_);
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2590_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2543_, v_packages_2588_, v___x_2605_, v___x_2606_, v___x_2591_, v_snd_2553_);
lean_dec_ref(v_packages_2588_);
return v___x_2607_;
}
}
}
}
}
v___jp_2609_:
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = lean_array_get_size(v___y_2610_);
v___x_2615_ = lean_nat_dec_lt(v___y_2612_, v___x_2614_);
if (v___x_2615_ == 0)
{
v___y_2551_ = v___y_2611_;
v_fst_2552_ = v_val_2613_;
v_snd_2553_ = v_a_2544_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_nat_dec_le(v___x_2614_, v___x_2614_);
if (v___x_2617_ == 0)
{
if (v___x_2615_ == 0)
{
v___y_2551_ = v___y_2611_;
v_fst_2552_ = v_val_2613_;
v_snd_2553_ = v_a_2544_;
goto v___jp_2550_;
}
else
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2614_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2610_, v___x_2618_, v___x_2619_, v___x_2616_, v___y_2542_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_dec_ref(v___x_2620_);
v___y_2551_ = v___y_2611_;
v_fst_2552_ = v_val_2613_;
v_snd_2553_ = v_a_2544_;
goto v___jp_2550_;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_val_2613_);
lean_dec_ref(v___y_2611_);
lean_dec(v_a_2544_);
lean_dec_ref(v_dep_2543_);
lean_dec_ref(v___y_2542_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
else
{
size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((size_t)0ULL);
v___x_2630_ = lean_usize_of_nat(v___x_2614_);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2610_, v___x_2629_, v___x_2630_, v___x_2616_, v___y_2542_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_dec_ref(v___x_2631_);
v___y_2551_ = v___y_2611_;
v_fst_2552_ = v_val_2613_;
v_snd_2553_ = v_a_2544_;
goto v___jp_2550_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_val_2613_);
lean_dec_ref(v___y_2611_);
lean_dec(v_a_2544_);
lean_dec_ref(v_dep_2543_);
lean_dec_ref(v___y_2542_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
v___jp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2641_);
v___x_2644_ = l_Lake_Manifest_load(v___y_2641_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set_tag(v___x_2647_, 1);
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
v___y_2610_ = v___x_2643_;
v___y_2611_ = v___y_2641_;
v___y_2612_ = v___x_2642_;
v_val_2613_ = v___x_2650_;
goto v___jp_2609_;
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
v_a_2653_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2644_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 0);
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
v___y_2610_ = v___x_2643_;
v___y_2611_ = v___y_2641_;
v___y_2612_ = v___x_2642_;
v_val_2613_ = v___x_2658_;
goto v___jp_2609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2665_, lean_object* v_dep_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2665_, v_dep_2666_, v_a_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2674_, v___y_2672_, v___y_2670_, v___y_2671_, v___y_2673_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2680_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v_fst_2678_ = lean_ctor_get(v_a_2677_, 0);
lean_inc_n(v_fst_2678_, 2);
v_snd_2679_ = lean_ctor_get(v_a_2677_, 1);
lean_inc(v_snd_2679_);
lean_dec(v_a_2677_);
v___x_2680_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2674_, v_fst_2678_, v_snd_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2697_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2697_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2697_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v_snd_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2695_; 
v_snd_2685_ = lean_ctor_get(v_a_2681_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2681_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v_a_2681_, 0);
lean_dec(v_unused_2696_);
v___x_2687_ = v_a_2681_;
v_isShared_2688_ = v_isSharedCheck_2695_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snd_2685_);
lean_dec(v_a_2681_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2695_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v_fst_2678_);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_fst_2678_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_snd_2685_);
v___x_2690_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2692_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2690_);
v___x_2692_ = v___x_2683_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_fst_2678_);
v_a_2698_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2680_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2680_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_dec_ref(v___y_2674_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2713_, lean_object* v_ws_2714_, lean_object* v_toUpdate_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___y_2719_; lean_object* v___y_2724_; lean_object* v_fst_2725_; lean_object* v_snd_2726_; lean_object* v_packages_2745_; lean_object* v___x_2746_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v_val_2751_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___x_2799_; lean_object* v_baseName_2800_; lean_object* v_dir_2801_; lean_object* v_config_2802_; lean_object* v_relManifestFile_2803_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v_fst_2808_; lean_object* v_snd_2809_; lean_object* v_packagesDir_x3f_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2871_; lean_object* v___y_2872_; uint8_t v___x_2875_; lean_object* v_rootName_2876_; lean_object* v_fst_2878_; lean_object* v_snd_2879_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v_val_2930_; lean_object* v___x_2956_; 
v_packages_2745_ = lean_ctor_get(v_ws_2714_, 4);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2799_ = lean_array_fget_borrowed(v_packages_2745_, v___x_2746_);
v_baseName_2800_ = lean_ctor_get(v___x_2799_, 1);
v_dir_2801_ = lean_ctor_get(v___x_2799_, 4);
v_config_2802_ = lean_ctor_get(v___x_2799_, 6);
v_relManifestFile_2803_ = lean_ctor_get(v___x_2799_, 9);
v___x_2875_ = 0;
lean_inc(v_baseName_2800_);
v_rootName_2876_ = l_Lean_Name_toString(v_baseName_2800_, v___x_2875_);
lean_inc_ref(v_relManifestFile_2803_);
lean_inc_ref(v_dir_2801_);
v___x_2927_ = l_Lake_joinRelative(v_dir_2801_, v_relManifestFile_2803_);
v___x_2928_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2956_ = l_Lake_Manifest_load(v___x_2927_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 1);
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v_val_2930_ = v___x_2962_;
goto v___jp_2929_;
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
v_a_2965_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2956_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2956_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 0);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
v_val_2930_ = v___x_2970_;
goto v___jp_2929_;
}
}
}
v___jp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___y_2719_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
v___jp_2723_:
{
if (lean_obj_tag(v_fst_2725_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_snd_2726_);
v_a_2727_ = lean_ctor_get(v_fst_2725_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_fst_2725_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2729_ = v_fst_2725_;
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v_fst_2725_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2731_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2732_ = lean_io_error_to_string(v_a_2727_);
v___x_2733_ = lean_string_append(v___x_2731_, v___x_2732_);
lean_dec_ref(v___x_2732_);
v___x_2734_ = 3;
v___x_2735_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*1, v___x_2734_);
lean_inc_ref(v___y_2724_);
v___x_2736_ = lean_apply_2(v___y_2724_, v___x_2735_, lean_box(0));
v___x_2737_ = lean_box(0);
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 1);
lean_ctor_set(v___x_2729_, 0, v___x_2737_);
v___x_2739_ = v___x_2729_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v_fst_2725_);
v___x_2742_ = lean_box(0);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v_snd_2726_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
}
v___jp_2747_:
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = lean_array_get_size(v___y_2748_);
v___x_2753_ = lean_nat_dec_lt(v___x_2746_, v___x_2752_);
if (v___x_2753_ == 0)
{
v___y_2724_ = v___y_2750_;
v_fst_2725_ = v_val_2751_;
v_snd_2726_ = v___y_2749_;
goto v___jp_2723_;
}
else
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_nat_dec_le(v___x_2752_, v___x_2752_);
if (v___x_2755_ == 0)
{
if (v___x_2753_ == 0)
{
v___y_2724_ = v___y_2750_;
v_fst_2725_ = v_val_2751_;
v_snd_2726_ = v___y_2749_;
goto v___jp_2723_;
}
else
{
size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = lean_usize_of_nat(v___x_2752_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2748_, v___x_2756_, v___x_2757_, v___x_2754_, v___y_2750_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_dec_ref(v___x_2758_);
v___y_2724_ = v___y_2750_;
v_fst_2725_ = v_val_2751_;
v_snd_2726_ = v___y_2749_;
goto v___jp_2723_;
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec_ref(v_val_2751_);
lean_dec(v___y_2749_);
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
else
{
size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = ((size_t)0ULL);
v___x_2768_ = lean_usize_of_nat(v___x_2752_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2748_, v___x_2767_, v___x_2768_, v___x_2754_, v___y_2750_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_dec_ref(v___x_2769_);
v___y_2724_ = v___y_2750_;
v_fst_2725_ = v_val_2751_;
v_snd_2726_ = v___y_2749_;
goto v___jp_2723_;
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v_val_2751_);
lean_dec(v___y_2749_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
v___jp_2778_:
{
if (lean_obj_tag(v___y_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_a_2783_ = lean_ctor_get(v___y_2782_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___y_2782_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___y_2782_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___y_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set_tag(v___x_2785_, 1);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v___y_2748_ = v___y_2779_;
v___y_2749_ = v___y_2780_;
v___y_2750_ = v___y_2781_;
v_val_2751_ = v___x_2788_;
goto v___jp_2747_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v___y_2782_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___y_2782_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___y_2782_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___y_2782_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 0);
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
v___y_2748_ = v___y_2779_;
v___y_2749_ = v___y_2780_;
v___y_2750_ = v___y_2781_;
v_val_2751_ = v___x_2796_;
goto v___jp_2747_;
}
}
}
}
v___jp_2804_:
{
lean_object* v_toWorkspaceConfig_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v_toWorkspaceConfig_2810_ = lean_ctor_get(v_config_2802_, 0);
v___x_2811_ = l_System_FilePath_normalize(v___y_2807_);
lean_inc_ref(v_toWorkspaceConfig_2810_);
v___x_2812_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2810_);
lean_inc_ref(v___x_2812_);
v___x_2813_ = l_System_FilePath_normalize(v___x_2812_);
v___x_2814_ = lean_string_dec_eq(v___x_2811_, v___x_2813_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v___x_2811_);
if (v___x_2814_ == 0)
{
if (v_fst_2808_ == 0)
{
lean_dec_ref(v___x_2812_);
lean_dec_ref(v___y_2805_);
v___y_2719_ = v_snd_2809_;
goto v___jp_2718_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2815_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2816_ = lean_string_append(v___x_2815_, v___y_2805_);
v___x_2817_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2818_ = lean_string_append(v___x_2816_, v___x_2817_);
lean_inc_ref(v_dir_2801_);
v___x_2819_ = l_Lake_joinRelative(v_dir_2801_, v___x_2812_);
v___x_2820_ = lean_string_append(v___x_2818_, v___x_2819_);
v___x_2821_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2822_ = lean_string_append(v___x_2820_, v___x_2821_);
v___x_2823_ = 1;
v___x_2824_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*1, v___x_2823_);
lean_inc_ref(v___y_2806_);
v___x_2825_ = lean_apply_2(v___y_2806_, v___x_2824_, lean_box(0));
v___x_2826_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2819_);
v___x_2827_ = l_Lake_createParentDirs(v___x_2819_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2828_; 
lean_dec_ref(v___x_2827_);
v___x_2828_ = lean_io_rename(v___y_2805_, v___x_2819_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___y_2805_);
v___y_2779_ = v___x_2826_;
v___y_2780_ = v_snd_2809_;
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___x_2828_;
goto v___jp_2778_;
}
else
{
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___y_2805_);
v___y_2779_ = v___x_2826_;
v___y_2780_ = v_snd_2809_;
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___x_2827_;
goto v___jp_2778_;
}
}
}
else
{
lean_dec_ref(v___x_2812_);
lean_dec_ref(v___y_2805_);
v___y_2719_ = v_snd_2809_;
goto v___jp_2718_;
}
}
v___jp_2829_:
{
if (lean_obj_tag(v_packagesDir_x3f_2830_) == 1)
{
lean_object* v_val_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_val_2833_ = lean_ctor_get(v_packagesDir_x3f_2830_, 0);
lean_inc_n(v_val_2833_, 2);
lean_dec_ref(v_packagesDir_x3f_2830_);
lean_inc_ref(v_dir_2801_);
v___x_2834_ = l_Lake_joinRelative(v_dir_2801_, v_val_2833_);
v___x_2835_ = l_System_FilePath_pathExists(v___x_2834_);
v___x_2836_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2837_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2837_ == 0)
{
v___y_2805_ = v___x_2834_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v_val_2833_;
v_fst_2808_ = v___x_2835_;
v_snd_2809_ = v___y_2831_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2839_ == 0)
{
if (v___x_2837_ == 0)
{
v___y_2805_ = v___x_2834_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v_val_2833_;
v_fst_2808_ = v___x_2835_;
v_snd_2809_ = v___y_2831_;
goto v___jp_2804_;
}
else
{
size_t v___x_2840_; size_t v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = ((size_t)0ULL);
v___x_2841_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2836_, v___x_2840_, v___x_2841_, v___x_2838_, v___y_2832_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref(v___x_2842_);
v___y_2805_ = v___x_2834_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v_val_2833_;
v_fst_2808_ = v___x_2835_;
v_snd_2809_ = v___y_2831_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v___x_2834_);
lean_dec(v_val_2833_);
lean_dec(v___y_2831_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
else
{
size_t v___x_2851_; size_t v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = ((size_t)0ULL);
v___x_2852_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2836_, v___x_2851_, v___x_2852_, v___x_2838_, v___y_2832_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref(v___x_2853_);
v___y_2805_ = v___x_2834_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v_val_2833_;
v_fst_2808_ = v___x_2835_;
v_snd_2809_ = v___y_2831_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v___x_2834_);
lean_dec(v_val_2833_);
lean_dec(v___y_2831_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec(v_packagesDir_x3f_2830_);
v___x_2862_ = lean_box(0);
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v___y_2831_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
v___jp_2865_:
{
lean_object* v_packagesDir_x3f_2869_; 
v_packagesDir_x3f_2869_ = lean_ctor_get(v___y_2866_, 2);
lean_inc(v_packagesDir_x3f_2869_);
lean_dec_ref(v___y_2866_);
v_packagesDir_x3f_2830_ = v_packagesDir_x3f_2869_;
v___y_2831_ = v___y_2867_;
v___y_2832_ = v___y_2868_;
goto v___jp_2829_;
}
v___jp_2870_:
{
if (lean_obj_tag(v___y_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v_snd_2874_; 
v_a_2873_ = lean_ctor_get(v___y_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___y_2872_);
v_snd_2874_ = lean_ctor_get(v_a_2873_, 1);
lean_inc(v_snd_2874_);
lean_dec(v_a_2873_);
v___y_2866_ = v___y_2871_;
v___y_2867_ = v_snd_2874_;
v___y_2868_ = v_a_2713_;
goto v___jp_2865_;
}
else
{
lean_dec_ref(v___y_2871_);
return v___y_2872_;
}
}
v___jp_2877_:
{
if (lean_obj_tag(v_fst_2878_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2912_; 
v_a_2880_ = lean_ctor_get(v_fst_2878_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_fst_2878_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2882_ = v_fst_2878_;
v_isShared_2883_ = v_isSharedCheck_2912_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v_fst_2878_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2912_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
if (lean_obj_tag(v_a_2880_) == 11)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_dec_ref(v_a_2880_);
v___x_2884_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2885_ = lean_string_append(v_rootName_2876_, v___x_2884_);
v___x_2886_ = 1;
v___x_2887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set_uint8(v___x_2887_, sizeof(void*)*1, v___x_2886_);
lean_inc_ref(v_a_2713_);
v___x_2888_ = lean_apply_2(v_a_2713_, v___x_2887_, lean_box(0));
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v_snd_2879_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2889_);
v___x_2891_ = v___x_2882_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2715_) == 0)
{
lean_object* v___x_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
lean_dec(v_snd_2879_);
lean_dec_ref(v_rootName_2876_);
v___x_2893_ = lean_io_error_to_string(v_a_2880_);
v___x_2894_ = 3;
v___x_2895_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*1, v___x_2894_);
lean_inc_ref(v_a_2713_);
v___x_2896_ = lean_apply_2(v_a_2713_, v___x_2895_, lean_box(0));
v___x_2897_ = lean_box(0);
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2897_);
v___x_2899_ = v___x_2882_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2901_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_2902_ = lean_string_append(v_rootName_2876_, v___x_2901_);
v___x_2903_ = lean_io_error_to_string(v_a_2880_);
v___x_2904_ = lean_string_append(v___x_2902_, v___x_2903_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = 2;
v___x_2906_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*1, v___x_2905_);
lean_inc_ref(v_a_2713_);
v___x_2907_ = lean_apply_2(v_a_2713_, v___x_2906_, lean_box(0));
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v_snd_2879_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2908_);
v___x_2910_ = v___x_2882_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2876_);
if (lean_obj_tag(v_toUpdate_2715_) == 0)
{
lean_object* v_a_2913_; lean_object* v_packagesDir_x3f_2914_; lean_object* v_packages_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_a_2913_ = lean_ctor_get(v_fst_2878_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v_fst_2878_);
v_packagesDir_x3f_2914_ = lean_ctor_get(v_a_2913_, 2);
v_packages_2915_ = lean_ctor_get(v_a_2913_, 3);
v___x_2916_ = lean_array_get_size(v_packages_2915_);
v___x_2917_ = lean_nat_dec_lt(v___x_2746_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_inc(v_packagesDir_x3f_2914_);
lean_dec(v_a_2913_);
v_packagesDir_x3f_2830_ = v_packagesDir_x3f_2914_;
v___y_2831_ = v_snd_2879_;
v___y_2832_ = v_a_2713_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_nat_dec_le(v___x_2916_, v___x_2916_);
if (v___x_2919_ == 0)
{
if (v___x_2917_ == 0)
{
lean_inc(v_packagesDir_x3f_2914_);
lean_dec(v_a_2913_);
v_packagesDir_x3f_2830_ = v_packagesDir_x3f_2914_;
v___y_2831_ = v_snd_2879_;
v___y_2832_ = v_a_2713_;
goto v___jp_2829_;
}
else
{
size_t v___x_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = lean_usize_of_nat(v___x_2916_);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2715_, v_packages_2915_, v___x_2920_, v___x_2921_, v___x_2918_, v_snd_2879_);
v___y_2871_ = v_a_2913_;
v___y_2872_ = v___x_2922_;
goto v___jp_2870_;
}
}
else
{
size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = lean_usize_of_nat(v___x_2916_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2715_, v_packages_2915_, v___x_2923_, v___x_2924_, v___x_2918_, v_snd_2879_);
v___y_2871_ = v_a_2913_;
v___y_2872_ = v___x_2925_;
goto v___jp_2870_;
}
}
}
else
{
lean_object* v_a_2926_; 
v_a_2926_ = lean_ctor_get(v_fst_2878_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v_fst_2878_);
v___y_2866_ = v_a_2926_;
v___y_2867_ = v_snd_2879_;
v___y_2868_ = v_a_2713_;
goto v___jp_2865_;
}
}
}
v___jp_2929_:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2931_ == 0)
{
v_fst_2878_ = v_val_2930_;
v_snd_2879_ = v_a_2716_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2933_ == 0)
{
if (v___x_2931_ == 0)
{
v_fst_2878_ = v_val_2930_;
v_snd_2879_ = v_a_2716_;
goto v___jp_2877_;
}
else
{
size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = ((size_t)0ULL);
v___x_2935_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2928_, v___x_2934_, v___x_2935_, v___x_2932_, v_a_2713_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_dec_ref(v___x_2936_);
v_fst_2878_ = v_val_2930_;
v_snd_2879_ = v_a_2716_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v_val_2930_);
lean_dec_ref(v_rootName_2876_);
lean_dec(v_a_2716_);
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
else
{
size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2928_, v___x_2945_, v___x_2946_, v___x_2932_, v_a_2713_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_dec_ref(v___x_2947_);
v_fst_2878_ = v_val_2930_;
v_snd_2879_ = v_a_2716_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_val_2930_);
lean_dec_ref(v_rootName_2876_);
lean_dec(v_a_2716_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_2973_, lean_object* v_ws_2974_, lean_object* v_toUpdate_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_2973_, v_ws_2974_, v_toUpdate_2975_, v_a_2976_);
lean_dec(v_toUpdate_2975_);
lean_dec_ref(v_ws_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_2979_, lean_object* v_ws_2980_, lean_object* v_rootDeps_2981_){
_start:
{
lean_object* v___y_2984_; lean_object* v_lakeEnv_2989_; lean_object* v_lakeArgs_x3f_2990_; lean_object* v_packages_2991_; lean_object* v___y_2993_; lean_object* v___y_2994_; uint8_t v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_3140_; lean_object* v___y_3141_; uint8_t v___y_3142_; lean_object* v___x_3145_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; uint8_t v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; uint8_t v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___x_3181_; lean_object* v_baseName_3182_; lean_object* v_dir_3183_; lean_object* v_config_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_lakeEnv_2989_ = lean_ctor_get(v_ws_2980_, 0);
lean_inc_ref(v_lakeEnv_2989_);
v_lakeArgs_x3f_2990_ = lean_ctor_get(v_ws_2980_, 3);
lean_inc(v_lakeArgs_x3f_2990_);
v_packages_2991_ = lean_ctor_get(v_ws_2980_, 4);
lean_inc_ref(v_packages_2991_);
lean_dec_ref(v_ws_2980_);
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3181_ = lean_array_fget(v_packages_2991_, v___x_3145_);
lean_dec_ref(v_packages_2991_);
v_baseName_3182_ = lean_ctor_get(v___x_3181_, 1);
lean_inc(v_baseName_3182_);
v_dir_3183_ = lean_ctor_get(v___x_3181_, 4);
lean_inc_ref_n(v_dir_3183_, 2);
v_config_3184_ = lean_ctor_get(v___x_3181_, 6);
lean_inc_ref(v_config_3184_);
lean_dec(v___x_3181_);
v___x_3185_ = l_Lake_toolchainFileName;
v___x_3186_ = l_System_FilePath_join(v_dir_3183_, v___x_3185_);
v___x_3187_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3186_);
lean_dec_ref(v___x_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3246_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3246_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3246_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_src_3193_; lean_object* v_tc_x3f_3194_; lean_object* v_clashes_3195_; uint8_t v_fixed_3196_; lean_object* v___y_3220_; uint8_t v_fixedToolchain_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_fixedToolchain_3234_ = lean_ctor_get_uint8(v_config_3184_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_3184_);
v___x_3235_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3236_ = lean_array_get_size(v_rootDeps_2981_);
v___x_3237_ = lean_nat_dec_lt(v___x_3145_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_inc(v_a_3188_);
v_src_3193_ = v_baseName_3182_;
v_tc_x3f_3194_ = v_a_3188_;
v_clashes_3195_ = v___x_3235_;
v_fixed_3196_ = v_fixedToolchain_3234_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
lean_inc(v_a_3188_);
lean_inc(v_baseName_3182_);
v___x_3238_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3238_, 0, v_baseName_3182_);
lean_ctor_set(v___x_3238_, 1, v_a_3188_);
lean_ctor_set(v___x_3238_, 2, v___x_3235_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*3, v_fixedToolchain_3234_);
v___x_3239_ = lean_nat_dec_le(v___x_3236_, v___x_3236_);
if (v___x_3239_ == 0)
{
if (v___x_3237_ == 0)
{
lean_dec_ref(v___x_3238_);
lean_inc(v_a_3188_);
v_src_3193_ = v_baseName_3182_;
v_tc_x3f_3194_ = v_a_3188_;
v_clashes_3195_ = v___x_3235_;
v_fixed_3196_ = v_fixedToolchain_3234_;
goto v___jp_3192_;
}
else
{
size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
lean_dec(v_baseName_3182_);
v___x_3240_ = ((size_t)0ULL);
v___x_3241_ = lean_usize_of_nat(v___x_3236_);
lean_inc_ref(v_dir_3183_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3183_, v_rootDeps_2981_, v___x_3240_, v___x_3241_, v___x_3238_, v_a_2979_);
v___y_3220_ = v___x_3242_;
goto v___jp_3219_;
}
}
else
{
size_t v___x_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
lean_dec(v_baseName_3182_);
v___x_3243_ = ((size_t)0ULL);
v___x_3244_ = lean_usize_of_nat(v___x_3236_);
lean_inc_ref(v_dir_3183_);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3183_, v_rootDeps_2981_, v___x_3243_, v___x_3244_, v___x_3238_, v_a_2979_);
v___y_3220_ = v___x_3245_;
goto v___jp_3219_;
}
}
v___jp_3192_:
{
lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = lean_array_get_size(v_clashes_3195_);
v___x_3198_ = lean_nat_dec_lt(v___x_3145_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_dec_ref(v_clashes_3195_);
lean_dec(v_src_3193_);
if (lean_obj_tag(v_tc_x3f_3194_) == 1)
{
lean_object* v_val_3199_; lean_object* v_rootToolchainFile_3200_; 
v_val_3199_ = lean_ctor_get(v_tc_x3f_3194_, 0);
lean_inc(v_val_3199_);
lean_dec_ref(v_tc_x3f_3194_);
v_rootToolchainFile_3200_ = l_Lake_joinRelative(v_dir_3183_, v___x_3185_);
if (lean_obj_tag(v_a_3188_) == 0)
{
lean_del_object(v___x_3190_);
v___y_3140_ = v_rootToolchainFile_3200_;
v___y_3141_ = v_val_3199_;
v___y_3142_ = v___x_3198_;
goto v___jp_3139_;
}
else
{
lean_object* v_val_3201_; uint8_t v___x_3202_; 
v_val_3201_ = lean_ctor_get(v_a_3188_, 0);
lean_inc(v_val_3201_);
lean_dec_ref(v_a_3188_);
lean_inc(v_val_3199_);
v___x_3202_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3201_, v_val_3199_);
if (v___x_3202_ == 0)
{
lean_del_object(v___x_3190_);
v___y_3140_ = v_rootToolchainFile_3200_;
v___y_3141_ = v_val_3199_;
v___y_3142_ = v___x_3202_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
lean_dec_ref(v_rootToolchainFile_3200_);
lean_dec(v_val_3199_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
v___x_3203_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2979_);
v___x_3204_ = lean_apply_2(v_a_2979_, v___x_3203_, lean_box(0));
v___x_3205_ = lean_box(0);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3205_);
v___x_3207_ = v___x_3190_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
lean_dec(v_tc_x3f_3194_);
lean_dec(v_a_3188_);
lean_dec_ref(v_dir_3183_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
v___x_3209_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2979_);
v___x_3210_ = lean_apply_2(v_a_2979_, v___x_3209_, lean_box(0));
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3210_);
v___x_3212_ = v___x_3190_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_del_object(v___x_3190_);
lean_dec(v_a_3188_);
lean_dec_ref(v_dir_3183_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
if (lean_obj_tag(v_tc_x3f_3194_) == 1)
{
if (v_fixed_3196_ == 0)
{
lean_object* v_val_3214_; lean_object* v___x_3215_; 
v_val_3214_ = lean_ctor_get(v_tc_x3f_3194_, 0);
lean_inc(v_val_3214_);
lean_dec_ref(v_tc_x3f_3194_);
v___x_3215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3173_ = v___x_3198_;
v___y_3174_ = v_val_3214_;
v___y_3175_ = v_src_3193_;
v___y_3176_ = v_clashes_3195_;
v___y_3177_ = v___x_3197_;
v___y_3178_ = v___x_3215_;
goto v___jp_3172_;
}
else
{
lean_object* v_val_3216_; lean_object* v___x_3217_; 
v_val_3216_ = lean_ctor_get(v_tc_x3f_3194_, 0);
lean_inc(v_val_3216_);
lean_dec_ref(v_tc_x3f_3194_);
v___x_3217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3173_ = v___x_3198_;
v___y_3174_ = v_val_3216_;
v___y_3175_ = v_src_3193_;
v___y_3176_ = v_clashes_3195_;
v___y_3177_ = v___x_3197_;
v___y_3178_ = v___x_3217_;
goto v___jp_3172_;
}
}
else
{
lean_object* v___x_3218_; 
lean_dec(v_tc_x3f_3194_);
lean_dec(v_src_3193_);
v___x_3218_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3147_ = v_clashes_3195_;
v___y_3148_ = v___x_3197_;
v___y_3149_ = v___x_3218_;
goto v___jp_3146_;
}
}
}
v___jp_3219_:
{
if (lean_obj_tag(v___y_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v_src_3222_; lean_object* v_tc_x3f_3223_; lean_object* v_clashes_3224_; uint8_t v_fixed_3225_; 
v_a_3221_ = lean_ctor_get(v___y_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___y_3220_);
v_src_3222_ = lean_ctor_get(v_a_3221_, 0);
lean_inc(v_src_3222_);
v_tc_x3f_3223_ = lean_ctor_get(v_a_3221_, 1);
lean_inc(v_tc_x3f_3223_);
v_clashes_3224_ = lean_ctor_get(v_a_3221_, 2);
lean_inc_ref(v_clashes_3224_);
v_fixed_3225_ = lean_ctor_get_uint8(v_a_3221_, sizeof(void*)*3);
lean_dec(v_a_3221_);
v_src_3193_ = v_src_3222_;
v_tc_x3f_3194_ = v_tc_x3f_3223_;
v_clashes_3195_ = v_clashes_3224_;
v_fixed_3196_ = v_fixed_3225_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3190_);
lean_dec(v_a_3188_);
lean_dec_ref(v_dir_3183_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
v_a_3226_ = lean_ctor_get(v___y_3220_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___y_3220_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___y_3220_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___y_3220_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_config_3184_);
lean_dec_ref(v_dir_3183_);
lean_dec(v_baseName_3182_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
v_a_3247_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3249_ = v___x_3187_;
v_isShared_3250_ = v_isSharedCheck_3259_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3187_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3259_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3251_ = lean_io_error_to_string(v_a_3247_);
v___x_3252_ = 3;
v___x_3253_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*1, v___x_3252_);
lean_inc_ref(v_a_2979_);
v___x_3254_ = lean_apply_2(v_a_2979_, v___x_3253_, lean_box(0));
v___x_3255_ = lean_box(0);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3255_);
v___x_3257_ = v___x_3249_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
v___jp_2983_:
{
uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2985_ = 2;
v___x_2986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2986_, 0, v___y_2984_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*1, v___x_2985_);
lean_inc_ref(v_a_2979_);
v___x_2987_ = lean_apply_2(v_a_2979_, v___x_2986_, lean_box(0));
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
v___jp_2992_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_inc_ref(v___y_2994_);
v___x_2997_ = lean_string_append(v___y_2994_, v___y_2996_);
v___x_2998_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2999_ = lean_string_append(v___x_2997_, v___x_2998_);
v___x_3000_ = 1;
v___x_3001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*1, v___x_3000_);
lean_inc_ref(v_a_2979_);
v___x_3002_ = lean_apply_2(v_a_2979_, v___x_3001_, lean_box(0));
v___x_3003_ = l_IO_FS_writeFile(v___y_2993_, v___y_2996_);
lean_dec_ref(v___y_2993_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_dec_ref(v___x_3003_);
if (lean_obj_tag(v_lakeArgs_x3f_2990_) == 1)
{
lean_object* v_elan_x3f_3004_; 
v_elan_x3f_3004_ = lean_ctor_get(v_lakeEnv_2989_, 2);
if (lean_obj_tag(v_elan_x3f_3004_) == 1)
{
lean_object* v_val_3005_; lean_object* v_val_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v_elan_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_val_3005_ = lean_ctor_get(v_lakeArgs_x3f_2990_, 0);
lean_inc(v_val_3005_);
lean_dec_ref(v_lakeArgs_x3f_2990_);
v_val_3006_ = lean_ctor_get(v_elan_x3f_3004_, 0);
v___x_3007_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2979_);
v___x_3008_ = lean_apply_2(v_a_2979_, v___x_3007_, lean_box(0));
v___x_3009_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_3010_ = lean_ctor_get(v_val_3006_, 1);
lean_inc_ref(v_elan_3010_);
v___x_3011_ = 1;
v___x_3012_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_3013_ = lean_unsigned_to_nat(4u);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_3013_);
lean_dec_ref(v___x_3014_);
v___x_3015_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_3016_ = lean_array_push(v___x_3015_, v___y_2996_);
v___x_3017_ = lean_array_push(v___x_3016_, v___x_3012_);
v___x_3018_ = l_Array_append___redArg(v___x_3017_, v_val_3005_);
lean_dec(v_val_3005_);
v___x_3019_ = lean_box(0);
v___x_3020_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2989_);
v___x_3021_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3021_, 0, v___x_3009_);
lean_ctor_set(v___x_3021_, 1, v_elan_3010_);
lean_ctor_set(v___x_3021_, 2, v___x_3018_);
lean_ctor_set(v___x_3021_, 3, v___x_3019_);
lean_ctor_set(v___x_3021_, 4, v___x_3020_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*5, v___x_3011_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*5 + 1, v___y_2995_);
v___x_3022_ = lean_io_process_spawn(v___x_3021_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = lean_io_process_child_wait(v___x_3009_, v_a_3023_);
lean_dec(v_a_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; uint32_t v___x_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = lean_unbox_uint32(v_a_3025_);
lean_dec(v_a_3025_);
v___x_3027_ = lean_uint32_to_uint8(v___x_3026_);
v___x_3028_ = lean_io_exit(v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3049_; 
v_a_3037_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3039_ = v___x_3028_;
v_isShared_3040_ = v_isSharedCheck_3049_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3028_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3049_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3041_ = lean_io_error_to_string(v_a_3037_);
v___x_3042_ = 3;
v___x_3043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*1, v___x_3042_);
lean_inc_ref(v_a_2979_);
v___x_3044_ = lean_apply_2(v_a_2979_, v___x_3043_, lean_box(0));
v___x_3045_ = lean_box(0);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3045_);
v___x_3047_ = v___x_3039_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3062_; 
v_a_3050_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3052_ = v___x_3024_;
v_isShared_3053_ = v_isSharedCheck_3062_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3024_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3062_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3054_ = lean_io_error_to_string(v_a_3050_);
v___x_3055_ = 3;
v___x_3056_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*1, v___x_3055_);
lean_inc_ref(v_a_2979_);
v___x_3057_ = lean_apply_2(v_a_2979_, v___x_3056_, lean_box(0));
v___x_3058_ = lean_box(0);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3058_);
v___x_3060_ = v___x_3052_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3075_; 
v_a_3063_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3065_ = v___x_3022_;
v_isShared_3066_ = v_isSharedCheck_3075_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3022_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3075_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3067_ = lean_io_error_to_string(v_a_3063_);
v___x_3068_ = 3;
v___x_3069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*1, v___x_3068_);
lean_inc_ref(v_a_2979_);
v___x_3070_ = lean_apply_2(v_a_2979_, v___x_3069_, lean_box(0));
v___x_3071_ = lean_box(0);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3071_);
v___x_3073_ = v___x_3065_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref(v_lakeArgs_x3f_2990_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_lakeEnv_2989_);
v___x_3076_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2979_);
v___x_3077_ = lean_apply_2(v_a_2979_, v___x_3076_, lean_box(0));
v___x_3078_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3079_ = lean_io_exit(v___x_3078_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3100_; 
v_a_3088_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3090_ = v___x_3079_;
v_isShared_3091_ = v_isSharedCheck_3100_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3079_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3100_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3092_ = lean_io_error_to_string(v_a_3088_);
v___x_3093_ = 3;
v___x_3094_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set_uint8(v___x_3094_, sizeof(void*)*1, v___x_3093_);
lean_inc_ref(v_a_2979_);
v___x_3095_ = lean_apply_2(v_a_2979_, v___x_3094_, lean_box(0));
v___x_3096_ = lean_box(0);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3096_);
v___x_3098_ = v___x_3090_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; 
lean_dec_ref(v___y_2996_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
v___x_3101_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2979_);
v___x_3102_ = lean_apply_2(v_a_2979_, v___x_3101_, lean_box(0));
v___x_3103_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3104_ = lean_io_exit(v___x_3103_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3125_; 
v_a_3113_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3115_ = v___x_3104_;
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3104_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3117_ = lean_io_error_to_string(v_a_3113_);
v___x_3118_ = 3;
v___x_3119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*1, v___x_3118_);
lean_inc_ref(v_a_2979_);
v___x_3120_ = lean_apply_2(v_a_2979_, v___x_3119_, lean_box(0));
v___x_3121_ = lean_box(0);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3121_);
v___x_3123_ = v___x_3115_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v___y_2996_);
lean_dec(v_lakeArgs_x3f_2990_);
lean_dec_ref(v_lakeEnv_2989_);
v_a_3126_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3128_ = v___x_3003_;
v_isShared_3129_ = v_isSharedCheck_3138_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3003_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3138_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3130_ = lean_io_error_to_string(v_a_3126_);
v___x_3131_ = 3;
v___x_3132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set_uint8(v___x_3132_, sizeof(void*)*1, v___x_3131_);
lean_inc_ref(v_a_2979_);
v___x_3133_ = lean_apply_2(v_a_2979_, v___x_3132_, lean_box(0));
v___x_3134_ = lean_box(0);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3134_);
v___x_3136_ = v___x_3128_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
v___jp_3139_:
{
lean_object* v___x_3143_; lean_object* v_toString_3144_; 
v___x_3143_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3144_ = lean_ctor_get(v___y_3141_, 0);
lean_inc_ref(v_toString_3144_);
lean_dec_ref(v___y_3141_);
v___y_2993_ = v___y_3140_;
v___y_2994_ = v___x_3143_;
v___y_2995_ = v___y_3142_;
v___y_2996_ = v_toString_3144_;
goto v___jp_2992_;
}
v___jp_3146_:
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_nat_dec_lt(v___x_3145_, v___y_3148_);
if (v___x_3150_ == 0)
{
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
v___y_2984_ = v___y_3149_;
goto v___jp_2983_;
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_nat_dec_le(v___y_3148_, v___y_3148_);
if (v___x_3151_ == 0)
{
if (v___x_3150_ == 0)
{
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
v___y_2984_ = v___y_3149_;
goto v___jp_2983_;
}
else
{
size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = lean_usize_of_nat(v___y_3148_);
lean_dec(v___y_3148_);
v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3147_, v___x_3152_, v___x_3153_, v___y_3149_);
lean_dec_ref(v___y_3147_);
v___y_2984_ = v___x_3154_;
goto v___jp_2983_;
}
}
else
{
size_t v___x_3155_; size_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = ((size_t)0ULL);
v___x_3156_ = lean_usize_of_nat(v___y_3148_);
lean_dec(v___y_3148_);
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3147_, v___x_3155_, v___x_3156_, v___y_3149_);
lean_dec_ref(v___y_3147_);
v___y_2984_ = v___x_3157_;
goto v___jp_2983_;
}
}
}
v___jp_3158_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_inc_ref(v___y_3161_);
v___x_3166_ = lean_string_append(v___y_3161_, v___y_3165_);
lean_dec_ref(v___y_3165_);
v___x_3167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3168_ = lean_string_append(v___x_3166_, v___x_3167_);
v___x_3169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3160_, v___y_3159_);
v___x_3170_ = lean_string_append(v___x_3168_, v___x_3169_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = lean_string_append(v___x_3170_, v___y_3162_);
v___y_3147_ = v___y_3164_;
v___y_3148_ = v___y_3163_;
v___y_3149_ = v___x_3171_;
goto v___jp_3146_;
}
v___jp_3172_:
{
lean_object* v___x_3179_; lean_object* v_toString_3180_; 
v___x_3179_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3180_ = lean_ctor_get(v___y_3174_, 0);
lean_inc_ref(v_toString_3180_);
lean_dec_ref(v___y_3174_);
v___y_3159_ = v___y_3173_;
v___y_3160_ = v___y_3175_;
v___y_3161_ = v___x_3179_;
v___y_3162_ = v___y_3178_;
v___y_3163_ = v___y_3177_;
v___y_3164_ = v___y_3176_;
v___y_3165_ = v_toString_3180_;
goto v___jp_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3260_, lean_object* v_ws_3261_, lean_object* v_rootDeps_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3260_, v_ws_3261_, v_rootDeps_3262_);
lean_dec_ref(v_rootDeps_3262_);
lean_dec_ref(v_a_3260_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(lean_object* v_msg_3265_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = lean_box(1);
v___x_3267_ = lean_panic_fn_borrowed(v___x_3266_, v_msg_3265_);
return v___x_3267_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3271_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2));
v___x_3272_ = lean_unsigned_to_nat(35u);
v___x_3273_ = lean_unsigned_to_nat(276u);
v___x_3274_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1));
v___x_3275_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3276_ = l_mkPanicMessageWithDecl(v___x_3275_, v___x_3274_, v___x_3273_, v___x_3272_, v___x_3271_);
return v___x_3276_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3277_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2));
v___x_3278_ = lean_unsigned_to_nat(21u);
v___x_3279_ = lean_unsigned_to_nat(277u);
v___x_3280_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1));
v___x_3281_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3282_ = l_mkPanicMessageWithDecl(v___x_3281_, v___x_3280_, v___x_3279_, v___x_3278_, v___x_3277_);
return v___x_3282_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3285_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6));
v___x_3286_ = lean_unsigned_to_nat(35u);
v___x_3287_ = lean_unsigned_to_nat(182u);
v___x_3288_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5));
v___x_3289_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3290_ = l_mkPanicMessageWithDecl(v___x_3289_, v___x_3288_, v___x_3287_, v___x_3286_, v___x_3285_);
return v___x_3290_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3291_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6));
v___x_3292_ = lean_unsigned_to_nat(21u);
v___x_3293_ = lean_unsigned_to_nat(183u);
v___x_3294_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5));
v___x_3295_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3296_ = l_mkPanicMessageWithDecl(v___x_3295_, v___x_3294_, v___x_3293_, v___x_3292_, v___x_3291_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(lean_object* v_k_3297_, lean_object* v_v_3298_, lean_object* v_t_3299_){
_start:
{
if (lean_obj_tag(v_t_3299_) == 0)
{
lean_object* v_size_3300_; lean_object* v_k_3301_; lean_object* v_v_3302_; lean_object* v_l_3303_; lean_object* v_r_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3661_; 
v_size_3300_ = lean_ctor_get(v_t_3299_, 0);
v_k_3301_ = lean_ctor_get(v_t_3299_, 1);
v_v_3302_ = lean_ctor_get(v_t_3299_, 2);
v_l_3303_ = lean_ctor_get(v_t_3299_, 3);
v_r_3304_ = lean_ctor_get(v_t_3299_, 4);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_t_3299_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3306_ = v_t_3299_;
v_isShared_3307_ = v_isSharedCheck_3661_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_r_3304_);
lean_inc(v_l_3303_);
lean_inc(v_v_3302_);
lean_inc(v_k_3301_);
lean_inc(v_size_3300_);
lean_dec(v_t_3299_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3661_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
uint8_t v___x_3308_; 
v___x_3308_ = lean_string_dec_lt(v_k_3297_, v_k_3301_);
if (v___x_3308_ == 0)
{
uint8_t v___x_3309_; 
v___x_3309_ = lean_string_dec_eq(v_k_3297_, v_k_3301_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; 
lean_dec(v_size_3300_);
v___x_3310_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v_k_3297_, v_v_3298_, v_r_3304_);
if (lean_obj_tag(v_l_3303_) == 0)
{
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_size_3311_; lean_object* v_size_3312_; lean_object* v_k_3313_; lean_object* v_v_3314_; lean_object* v_l_3315_; lean_object* v_r_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v_size_3311_ = lean_ctor_get(v_l_3303_, 0);
v_size_3312_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_size_3312_);
v_k_3313_ = lean_ctor_get(v___x_3310_, 1);
lean_inc(v_k_3313_);
v_v_3314_ = lean_ctor_get(v___x_3310_, 2);
lean_inc(v_v_3314_);
v_l_3315_ = lean_ctor_get(v___x_3310_, 3);
lean_inc(v_l_3315_);
v_r_3316_ = lean_ctor_get(v___x_3310_, 4);
lean_inc(v_r_3316_);
v___x_3317_ = lean_unsigned_to_nat(3u);
v___x_3318_ = lean_nat_mul(v___x_3317_, v_size_3311_);
v___x_3319_ = lean_nat_dec_lt(v___x_3318_, v_size_3312_);
lean_dec(v___x_3318_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec(v_r_3316_);
lean_dec(v_l_3315_);
lean_dec(v_v_3314_);
lean_dec(v_k_3313_);
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = lean_nat_add(v___x_3320_, v_size_3311_);
v___x_3322_ = lean_nat_add(v___x_3321_, v_size_3312_);
lean_dec(v_size_3312_);
lean_dec(v___x_3321_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3310_);
lean_ctor_set(v___x_3306_, 0, v___x_3322_);
v___x_3324_ = v___x_3306_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3325_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3325_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3325_, 4, v___x_3310_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
else
{
lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3395_; 
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; lean_object* v_unused_3399_; lean_object* v_unused_3400_; 
v_unused_3396_ = lean_ctor_get(v___x_3310_, 4);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v___x_3310_, 3);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v___x_3310_, 2);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v___x_3310_, 1);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v___x_3310_, 0);
lean_dec(v_unused_3400_);
v___x_3327_ = v___x_3310_;
v_isShared_3328_ = v_isSharedCheck_3395_;
goto v_resetjp_3326_;
}
else
{
lean_dec(v___x_3310_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3395_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
if (lean_obj_tag(v_l_3315_) == 0)
{
if (lean_obj_tag(v_r_3316_) == 0)
{
lean_object* v_size_3329_; lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v_l_3332_; lean_object* v_r_3333_; lean_object* v_size_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v_size_3329_ = lean_ctor_get(v_l_3315_, 0);
v_k_3330_ = lean_ctor_get(v_l_3315_, 1);
v_v_3331_ = lean_ctor_get(v_l_3315_, 2);
v_l_3332_ = lean_ctor_get(v_l_3315_, 3);
v_r_3333_ = lean_ctor_get(v_l_3315_, 4);
v_size_3334_ = lean_ctor_get(v_r_3316_, 0);
v___x_3335_ = lean_unsigned_to_nat(2u);
v___x_3336_ = lean_nat_mul(v___x_3335_, v_size_3334_);
v___x_3337_ = lean_nat_dec_lt(v_size_3329_, v___x_3336_);
lean_dec(v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3366_; 
lean_inc(v_r_3333_);
lean_inc(v_l_3332_);
lean_inc(v_v_3331_);
lean_inc(v_k_3330_);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_l_3315_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; lean_object* v_unused_3368_; lean_object* v_unused_3369_; lean_object* v_unused_3370_; lean_object* v_unused_3371_; 
v_unused_3367_ = lean_ctor_get(v_l_3315_, 4);
lean_dec(v_unused_3367_);
v_unused_3368_ = lean_ctor_get(v_l_3315_, 3);
lean_dec(v_unused_3368_);
v_unused_3369_ = lean_ctor_get(v_l_3315_, 2);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v_l_3315_, 1);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v_l_3315_, 0);
lean_dec(v_unused_3371_);
v___x_3339_ = v_l_3315_;
v_isShared_3340_ = v_isSharedCheck_3366_;
goto v_resetjp_3338_;
}
else
{
lean_dec(v_l_3315_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3366_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3356_; 
v___x_3341_ = lean_unsigned_to_nat(1u);
v___x_3342_ = lean_nat_add(v___x_3341_, v_size_3311_);
v___x_3343_ = lean_nat_add(v___x_3342_, v_size_3312_);
lean_dec(v_size_3312_);
if (lean_obj_tag(v_l_3332_) == 0)
{
lean_object* v_size_3364_; 
v_size_3364_ = lean_ctor_get(v_l_3332_, 0);
lean_inc(v_size_3364_);
v___y_3356_ = v_size_3364_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___y_3356_ = v___x_3365_;
goto v___jp_3355_;
}
v___jp_3344_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_nat_add(v___y_3345_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec(v___y_3345_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 4, v_r_3316_);
lean_ctor_set(v___x_3339_, 3, v_r_3333_);
lean_ctor_set(v___x_3339_, 2, v_v_3314_);
lean_ctor_set(v___x_3339_, 1, v_k_3313_);
lean_ctor_set(v___x_3339_, 0, v___x_3348_);
v___x_3350_ = v___x_3339_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_k_3313_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_v_3314_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v_r_3333_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v_r_3316_);
v___x_3350_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3352_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v___x_3350_);
lean_ctor_set(v___x_3327_, 3, v___y_3346_);
lean_ctor_set(v___x_3327_, 2, v_v_3331_);
lean_ctor_set(v___x_3327_, 1, v_k_3330_);
lean_ctor_set(v___x_3327_, 0, v___x_3343_);
v___x_3352_ = v___x_3327_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v___y_3346_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_nat_add(v___x_3342_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec(v___x_3342_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_l_3332_);
lean_ctor_set(v___x_3306_, 0, v___x_3357_);
v___x_3359_ = v___x_3306_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_l_3332_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_nat_add(v___x_3341_, v_size_3334_);
if (lean_obj_tag(v_r_3333_) == 0)
{
lean_object* v_size_3361_; 
v_size_3361_ = lean_ctor_get(v_r_3333_, 0);
lean_inc(v_size_3361_);
v___y_3345_ = v___x_3360_;
v___y_3346_ = v___x_3359_;
v___y_3347_ = v_size_3361_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_unsigned_to_nat(0u);
v___y_3345_ = v___x_3360_;
v___y_3346_ = v___x_3359_;
v___y_3347_ = v___x_3362_;
goto v___jp_3344_;
}
}
}
}
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_del_object(v___x_3306_);
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_add(v___x_3372_, v_size_3311_);
v___x_3374_ = lean_nat_add(v___x_3373_, v_size_3312_);
lean_dec(v_size_3312_);
v___x_3375_ = lean_nat_add(v___x_3373_, v_size_3329_);
lean_dec(v___x_3373_);
lean_inc_ref(v_l_3303_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v_l_3315_);
lean_ctor_set(v___x_3327_, 3, v_l_3303_);
lean_ctor_set(v___x_3327_, 2, v_v_3302_);
lean_ctor_set(v___x_3327_, 1, v_k_3301_);
lean_ctor_set(v___x_3327_, 0, v___x_3375_);
v___x_3377_ = v___x_3327_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_l_3315_);
v___x_3377_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_isSharedCheck_3384_ = !lean_is_exclusive(v_l_3303_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; lean_object* v_unused_3386_; lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; 
v_unused_3385_ = lean_ctor_get(v_l_3303_, 4);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_l_3303_, 3);
lean_dec(v_unused_3386_);
v_unused_3387_ = lean_ctor_get(v_l_3303_, 2);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v_l_3303_, 1);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_l_3303_, 0);
lean_dec(v_unused_3389_);
v___x_3379_ = v_l_3303_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_l_3303_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 4, v_r_3316_);
lean_ctor_set(v___x_3379_, 3, v___x_3377_);
lean_ctor_set(v___x_3379_, 2, v_v_3314_);
lean_ctor_set(v___x_3379_, 1, v_k_3313_);
lean_ctor_set(v___x_3379_, 0, v___x_3374_);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_k_3313_);
lean_ctor_set(v_reuseFailAlloc_3383_, 2, v_v_3314_);
lean_ctor_set(v_reuseFailAlloc_3383_, 3, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3383_, 4, v_r_3316_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec_ref(v_l_3315_);
lean_del_object(v___x_3327_);
lean_dec(v_v_3314_);
lean_dec(v_k_3313_);
lean_dec(v_size_3312_);
lean_dec_ref(v_l_3303_);
lean_del_object(v___x_3306_);
lean_dec(v_v_3302_);
lean_dec(v_k_3301_);
v___x_3391_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3);
v___x_3392_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3391_);
return v___x_3392_;
}
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_del_object(v___x_3327_);
lean_dec(v_r_3316_);
lean_dec(v_v_3314_);
lean_dec(v_k_3313_);
lean_dec(v_size_3312_);
lean_dec_ref(v_l_3303_);
lean_del_object(v___x_3306_);
lean_dec(v_v_3302_);
lean_dec(v_k_3301_);
v___x_3393_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4);
v___x_3394_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3393_);
return v___x_3394_;
}
}
}
}
else
{
lean_object* v_size_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v_size_3401_ = lean_ctor_get(v_l_3303_, 0);
v___x_3402_ = lean_unsigned_to_nat(1u);
v___x_3403_ = lean_nat_add(v___x_3402_, v_size_3401_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3310_);
lean_ctor_set(v___x_3306_, 0, v___x_3403_);
v___x_3405_ = v___x_3306_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v___x_3310_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_l_3407_; 
v_l_3407_ = lean_ctor_get(v___x_3310_, 3);
lean_inc(v_l_3407_);
if (lean_obj_tag(v_l_3407_) == 0)
{
lean_object* v_r_3408_; 
v_r_3408_ = lean_ctor_get(v___x_3310_, 4);
lean_inc(v_r_3408_);
if (lean_obj_tag(v_r_3408_) == 0)
{
lean_object* v_size_3409_; lean_object* v_k_3410_; lean_object* v_v_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3425_; 
v_size_3409_ = lean_ctor_get(v___x_3310_, 0);
v_k_3410_ = lean_ctor_get(v___x_3310_, 1);
v_v_3411_ = lean_ctor_get(v___x_3310_, 2);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3426_ = lean_ctor_get(v___x_3310_, 4);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v___x_3310_, 3);
lean_dec(v_unused_3427_);
v___x_3413_ = v___x_3310_;
v_isShared_3414_ = v_isSharedCheck_3425_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_v_3411_);
lean_inc(v_k_3410_);
lean_inc(v_size_3409_);
lean_dec(v___x_3310_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3425_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v_size_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
v_size_3415_ = lean_ctor_get(v_l_3407_, 0);
v___x_3416_ = lean_unsigned_to_nat(1u);
v___x_3417_ = lean_nat_add(v___x_3416_, v_size_3409_);
lean_dec(v_size_3409_);
v___x_3418_ = lean_nat_add(v___x_3416_, v_size_3415_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 4, v_l_3407_);
lean_ctor_set(v___x_3413_, 3, v_l_3303_);
lean_ctor_set(v___x_3413_, 2, v_v_3302_);
lean_ctor_set(v___x_3413_, 1, v_k_3301_);
lean_ctor_set(v___x_3413_, 0, v___x_3418_);
v___x_3420_ = v___x_3413_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_l_3407_);
v___x_3420_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_r_3408_);
lean_ctor_set(v___x_3306_, 3, v___x_3420_);
lean_ctor_set(v___x_3306_, 2, v_v_3411_);
lean_ctor_set(v___x_3306_, 1, v_k_3410_);
lean_ctor_set(v___x_3306_, 0, v___x_3417_);
v___x_3422_ = v___x_3306_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_k_3410_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_v_3411_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_r_3408_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v_k_3428_; lean_object* v_v_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3453_; 
v_k_3428_ = lean_ctor_get(v___x_3310_, 1);
v_v_3429_ = lean_ctor_get(v___x_3310_, 2);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3453_ == 0)
{
lean_object* v_unused_3454_; lean_object* v_unused_3455_; lean_object* v_unused_3456_; 
v_unused_3454_ = lean_ctor_get(v___x_3310_, 4);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v___x_3310_, 3);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v___x_3310_, 0);
lean_dec(v_unused_3456_);
v___x_3431_ = v___x_3310_;
v_isShared_3432_ = v_isSharedCheck_3453_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_v_3429_);
lean_inc(v_k_3428_);
lean_dec(v___x_3310_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3453_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_k_3433_; lean_object* v_v_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3449_; 
v_k_3433_ = lean_ctor_get(v_l_3407_, 1);
v_v_3434_ = lean_ctor_get(v_l_3407_, 2);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_l_3407_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; lean_object* v_unused_3451_; lean_object* v_unused_3452_; 
v_unused_3450_ = lean_ctor_get(v_l_3407_, 4);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v_l_3407_, 3);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_l_3407_, 0);
lean_dec(v_unused_3452_);
v___x_3436_ = v_l_3407_;
v_isShared_3437_ = v_isSharedCheck_3449_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_v_3434_);
lean_inc(v_k_3433_);
lean_dec(v_l_3407_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3449_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3438_ = lean_unsigned_to_nat(3u);
v___x_3439_ = lean_unsigned_to_nat(1u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_r_3408_);
lean_ctor_set(v___x_3436_, 3, v_r_3408_);
lean_ctor_set(v___x_3436_, 2, v_v_3302_);
lean_ctor_set(v___x_3436_, 1, v_k_3301_);
lean_ctor_set(v___x_3436_, 0, v___x_3439_);
v___x_3441_ = v___x_3436_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_r_3408_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_r_3408_);
v___x_3441_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3443_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 3, v_r_3408_);
lean_ctor_set(v___x_3431_, 0, v___x_3439_);
v___x_3443_ = v___x_3431_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_3428_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_3429_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_r_3408_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_r_3408_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3443_);
lean_ctor_set(v___x_3306_, 3, v___x_3441_);
lean_ctor_set(v___x_3306_, 2, v_v_3434_);
lean_ctor_set(v___x_3306_, 1, v_k_3433_);
lean_ctor_set(v___x_3306_, 0, v___x_3438_);
v___x_3445_ = v___x_3306_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_k_3433_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_v_3434_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3457_; 
v_r_3457_ = lean_ctor_get(v___x_3310_, 4);
lean_inc(v_r_3457_);
if (lean_obj_tag(v_r_3457_) == 0)
{
lean_object* v_k_3458_; lean_object* v_v_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3471_; 
v_k_3458_ = lean_ctor_get(v___x_3310_, 1);
v_v_3459_ = lean_ctor_get(v___x_3310_, 2);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; lean_object* v_unused_3474_; 
v_unused_3472_ = lean_ctor_get(v___x_3310_, 4);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v___x_3310_, 3);
lean_dec(v_unused_3473_);
v_unused_3474_ = lean_ctor_get(v___x_3310_, 0);
lean_dec(v_unused_3474_);
v___x_3461_ = v___x_3310_;
v_isShared_3462_ = v_isSharedCheck_3471_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_v_3459_);
lean_inc(v_k_3458_);
lean_dec(v___x_3310_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3471_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = lean_unsigned_to_nat(3u);
v___x_3464_ = lean_unsigned_to_nat(1u);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 4, v_l_3407_);
lean_ctor_set(v___x_3461_, 2, v_v_3302_);
lean_ctor_set(v___x_3461_, 1, v_k_3301_);
lean_ctor_set(v___x_3461_, 0, v___x_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_l_3407_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_l_3407_);
v___x_3466_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_r_3457_);
lean_ctor_set(v___x_3306_, 3, v___x_3466_);
lean_ctor_set(v___x_3306_, 2, v_v_3459_);
lean_ctor_set(v___x_3306_, 1, v_k_3458_);
lean_ctor_set(v___x_3306_, 0, v___x_3463_);
v___x_3468_ = v___x_3306_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_3458_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_3459_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_r_3457_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_unsigned_to_nat(2u);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3310_);
lean_ctor_set(v___x_3306_, 3, v_r_3457_);
lean_ctor_set(v___x_3306_, 0, v___x_3475_);
v___x_3477_ = v___x_3306_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_r_3457_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v___x_3310_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = lean_unsigned_to_nat(1u);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3310_);
lean_ctor_set(v___x_3306_, 3, v___x_3310_);
lean_ctor_set(v___x_3306_, 0, v___x_3479_);
v___x_3481_ = v___x_3306_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v___x_3310_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v___x_3484_; 
lean_dec(v_v_3302_);
lean_dec(v_k_3301_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 2, v_v_3298_);
lean_ctor_set(v___x_3306_, 1, v_k_3297_);
v___x_3484_ = v___x_3306_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_size_3300_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_3297_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_3298_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_r_3304_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
else
{
lean_object* v___x_3486_; 
lean_dec(v_size_3300_);
v___x_3486_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v_k_3297_, v_v_3298_, v_l_3303_);
if (lean_obj_tag(v_r_3304_) == 0)
{
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_size_3487_; lean_object* v_size_3488_; lean_object* v_k_3489_; lean_object* v_v_3490_; lean_object* v_l_3491_; lean_object* v_r_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v_size_3487_ = lean_ctor_get(v_r_3304_, 0);
v_size_3488_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_size_3488_);
v_k_3489_ = lean_ctor_get(v___x_3486_, 1);
lean_inc(v_k_3489_);
v_v_3490_ = lean_ctor_get(v___x_3486_, 2);
lean_inc(v_v_3490_);
v_l_3491_ = lean_ctor_get(v___x_3486_, 3);
lean_inc(v_l_3491_);
v_r_3492_ = lean_ctor_get(v___x_3486_, 4);
lean_inc(v_r_3492_);
v___x_3493_ = lean_unsigned_to_nat(3u);
v___x_3494_ = lean_nat_mul(v___x_3493_, v_size_3487_);
v___x_3495_ = lean_nat_dec_lt(v___x_3494_, v_size_3488_);
lean_dec(v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
lean_dec(v_r_3492_);
lean_dec(v_l_3491_);
lean_dec(v_v_3490_);
lean_dec(v_k_3489_);
v___x_3496_ = lean_unsigned_to_nat(1u);
v___x_3497_ = lean_nat_add(v___x_3496_, v_size_3488_);
lean_dec(v_size_3488_);
v___x_3498_ = lean_nat_add(v___x_3497_, v_size_3487_);
lean_dec(v___x_3497_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 3, v___x_3486_);
lean_ctor_set(v___x_3306_, 0, v___x_3498_);
v___x_3500_ = v___x_3306_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_r_3304_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
else
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3573_; 
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; lean_object* v_unused_3575_; lean_object* v_unused_3576_; lean_object* v_unused_3577_; lean_object* v_unused_3578_; 
v_unused_3574_ = lean_ctor_get(v___x_3486_, 4);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v___x_3486_, 3);
lean_dec(v_unused_3575_);
v_unused_3576_ = lean_ctor_get(v___x_3486_, 2);
lean_dec(v_unused_3576_);
v_unused_3577_ = lean_ctor_get(v___x_3486_, 1);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v___x_3486_, 0);
lean_dec(v_unused_3578_);
v___x_3503_ = v___x_3486_;
v_isShared_3504_ = v_isSharedCheck_3573_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v___x_3486_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3573_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
if (lean_obj_tag(v_l_3491_) == 0)
{
if (lean_obj_tag(v_r_3492_) == 0)
{
lean_object* v_size_3505_; lean_object* v_size_3506_; lean_object* v_k_3507_; lean_object* v_v_3508_; lean_object* v_l_3509_; lean_object* v_r_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v_size_3505_ = lean_ctor_get(v_l_3491_, 0);
v_size_3506_ = lean_ctor_get(v_r_3492_, 0);
v_k_3507_ = lean_ctor_get(v_r_3492_, 1);
v_v_3508_ = lean_ctor_get(v_r_3492_, 2);
v_l_3509_ = lean_ctor_get(v_r_3492_, 3);
v_r_3510_ = lean_ctor_get(v_r_3492_, 4);
v___x_3511_ = lean_unsigned_to_nat(2u);
v___x_3512_ = lean_nat_mul(v___x_3511_, v_size_3505_);
v___x_3513_ = lean_nat_dec_lt(v_size_3506_, v___x_3512_);
lean_dec(v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3543_; 
lean_inc(v_r_3510_);
lean_inc(v_l_3509_);
lean_inc(v_v_3508_);
lean_inc(v_k_3507_);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_r_3492_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; lean_object* v_unused_3545_; lean_object* v_unused_3546_; lean_object* v_unused_3547_; lean_object* v_unused_3548_; 
v_unused_3544_ = lean_ctor_get(v_r_3492_, 4);
lean_dec(v_unused_3544_);
v_unused_3545_ = lean_ctor_get(v_r_3492_, 3);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_r_3492_, 2);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_r_3492_, 1);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_r_3492_, 0);
lean_dec(v_unused_3548_);
v___x_3515_ = v_r_3492_;
v_isShared_3516_ = v_isSharedCheck_3543_;
goto v_resetjp_3514_;
}
else
{
lean_dec(v_r_3492_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3543_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___x_3531_; lean_object* v___y_3533_; 
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v___x_3517_, v_size_3488_);
lean_dec(v_size_3488_);
v___x_3519_ = lean_nat_add(v___x_3518_, v_size_3487_);
lean_dec(v___x_3518_);
v___x_3531_ = lean_nat_add(v___x_3517_, v_size_3505_);
if (lean_obj_tag(v_l_3509_) == 0)
{
lean_object* v_size_3541_; 
v_size_3541_ = lean_ctor_get(v_l_3509_, 0);
lean_inc(v_size_3541_);
v___y_3533_ = v_size_3541_;
goto v___jp_3532_;
}
else
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_unsigned_to_nat(0u);
v___y_3533_ = v___x_3542_;
goto v___jp_3532_;
}
v___jp_3520_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_nat_add(v___y_3521_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec(v___y_3521_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 4, v_r_3304_);
lean_ctor_set(v___x_3515_, 3, v_r_3510_);
lean_ctor_set(v___x_3515_, 2, v_v_3302_);
lean_ctor_set(v___x_3515_, 1, v_k_3301_);
lean_ctor_set(v___x_3515_, 0, v___x_3524_);
v___x_3526_ = v___x_3515_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3530_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3530_, 3, v_r_3510_);
lean_ctor_set(v_reuseFailAlloc_3530_, 4, v_r_3304_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 4, v___x_3526_);
lean_ctor_set(v___x_3503_, 3, v___y_3522_);
lean_ctor_set(v___x_3503_, 2, v_v_3508_);
lean_ctor_set(v___x_3503_, 1, v_k_3507_);
lean_ctor_set(v___x_3503_, 0, v___x_3519_);
v___x_3528_ = v___x_3503_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_k_3507_);
lean_ctor_set(v_reuseFailAlloc_3529_, 2, v_v_3508_);
lean_ctor_set(v_reuseFailAlloc_3529_, 3, v___y_3522_);
lean_ctor_set(v_reuseFailAlloc_3529_, 4, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
v___jp_3532_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = lean_nat_add(v___x_3531_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec(v___x_3531_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_l_3509_);
lean_ctor_set(v___x_3306_, 3, v_l_3491_);
lean_ctor_set(v___x_3306_, 2, v_v_3490_);
lean_ctor_set(v___x_3306_, 1, v_k_3489_);
lean_ctor_set(v___x_3306_, 0, v___x_3534_);
v___x_3536_ = v___x_3306_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_k_3489_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_v_3490_);
lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_l_3491_);
lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_l_3509_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; 
v___x_3537_ = lean_nat_add(v___x_3517_, v_size_3487_);
if (lean_obj_tag(v_r_3510_) == 0)
{
lean_object* v_size_3538_; 
v_size_3538_ = lean_ctor_get(v_r_3510_, 0);
lean_inc(v_size_3538_);
v___y_3521_ = v___x_3537_;
v___y_3522_ = v___x_3536_;
v___y_3523_ = v_size_3538_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_unsigned_to_nat(0u);
v___y_3521_ = v___x_3537_;
v___y_3522_ = v___x_3536_;
v___y_3523_ = v___x_3539_;
goto v___jp_3520_;
}
}
}
}
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
lean_del_object(v___x_3306_);
v___x_3549_ = lean_unsigned_to_nat(1u);
v___x_3550_ = lean_nat_add(v___x_3549_, v_size_3488_);
lean_dec(v_size_3488_);
v___x_3551_ = lean_nat_add(v___x_3550_, v_size_3487_);
lean_dec(v___x_3550_);
v___x_3552_ = lean_nat_add(v___x_3549_, v_size_3487_);
v___x_3553_ = lean_nat_add(v___x_3552_, v_size_3506_);
lean_dec(v___x_3552_);
lean_inc_ref(v_r_3304_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 4, v_r_3304_);
lean_ctor_set(v___x_3503_, 3, v_r_3492_);
lean_ctor_set(v___x_3503_, 2, v_v_3302_);
lean_ctor_set(v___x_3503_, 1, v_k_3301_);
lean_ctor_set(v___x_3503_, 0, v___x_3553_);
v___x_3555_ = v___x_3503_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_r_3492_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_r_3304_);
v___x_3555_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_isSharedCheck_3562_ = !lean_is_exclusive(v_r_3304_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; lean_object* v_unused_3566_; lean_object* v_unused_3567_; 
v_unused_3563_ = lean_ctor_get(v_r_3304_, 4);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_r_3304_, 3);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_r_3304_, 2);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_r_3304_, 1);
lean_dec(v_unused_3566_);
v_unused_3567_ = lean_ctor_get(v_r_3304_, 0);
lean_dec(v_unused_3567_);
v___x_3557_ = v_r_3304_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_dec(v_r_3304_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 4, v___x_3555_);
lean_ctor_set(v___x_3557_, 3, v_l_3491_);
lean_ctor_set(v___x_3557_, 2, v_v_3490_);
lean_ctor_set(v___x_3557_, 1, v_k_3489_);
lean_ctor_set(v___x_3557_, 0, v___x_3551_);
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_k_3489_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v_v_3490_);
lean_ctor_set(v_reuseFailAlloc_3561_, 3, v_l_3491_);
lean_ctor_set(v_reuseFailAlloc_3561_, 4, v___x_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref(v_l_3491_);
lean_del_object(v___x_3503_);
lean_dec(v_v_3490_);
lean_dec(v_k_3489_);
lean_dec(v_size_3488_);
lean_dec_ref(v_r_3304_);
lean_del_object(v___x_3306_);
lean_dec(v_v_3302_);
lean_dec(v_k_3301_);
v___x_3569_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7);
v___x_3570_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3569_);
return v___x_3570_;
}
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_del_object(v___x_3503_);
lean_dec(v_r_3492_);
lean_dec(v_v_3490_);
lean_dec(v_k_3489_);
lean_dec(v_size_3488_);
lean_dec_ref(v_r_3304_);
lean_del_object(v___x_3306_);
lean_dec(v_v_3302_);
lean_dec(v_k_3301_);
v___x_3571_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8);
v___x_3572_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3571_);
return v___x_3572_;
}
}
}
}
else
{
lean_object* v_size_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v_size_3579_ = lean_ctor_get(v_r_3304_, 0);
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = lean_nat_add(v___x_3580_, v_size_3579_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 3, v___x_3486_);
lean_ctor_set(v___x_3306_, 0, v___x_3581_);
v___x_3583_ = v___x_3306_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_r_3304_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
else
{
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_l_3585_; 
v_l_3585_ = lean_ctor_get(v___x_3486_, 3);
lean_inc(v_l_3585_);
if (lean_obj_tag(v_l_3585_) == 0)
{
lean_object* v_r_3586_; 
v_r_3586_ = lean_ctor_get(v___x_3486_, 4);
lean_inc(v_r_3586_);
if (lean_obj_tag(v_r_3586_) == 0)
{
lean_object* v_size_3587_; lean_object* v_k_3588_; lean_object* v_v_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3603_; 
v_size_3587_ = lean_ctor_get(v___x_3486_, 0);
v_k_3588_ = lean_ctor_get(v___x_3486_, 1);
v_v_3589_ = lean_ctor_get(v___x_3486_, 2);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; lean_object* v_unused_3605_; 
v_unused_3604_ = lean_ctor_get(v___x_3486_, 4);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v___x_3486_, 3);
lean_dec(v_unused_3605_);
v___x_3591_ = v___x_3486_;
v_isShared_3592_ = v_isSharedCheck_3603_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_v_3589_);
lean_inc(v_k_3588_);
lean_inc(v_size_3587_);
lean_dec(v___x_3486_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3603_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_size_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
v_size_3593_ = lean_ctor_get(v_r_3586_, 0);
v___x_3594_ = lean_unsigned_to_nat(1u);
v___x_3595_ = lean_nat_add(v___x_3594_, v_size_3587_);
lean_dec(v_size_3587_);
v___x_3596_ = lean_nat_add(v___x_3594_, v_size_3593_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 4, v_r_3304_);
lean_ctor_set(v___x_3591_, 3, v_r_3586_);
lean_ctor_set(v___x_3591_, 2, v_v_3302_);
lean_ctor_set(v___x_3591_, 1, v_k_3301_);
lean_ctor_set(v___x_3591_, 0, v___x_3596_);
v___x_3598_ = v___x_3591_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_r_3586_);
lean_ctor_set(v_reuseFailAlloc_3602_, 4, v_r_3304_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3598_);
lean_ctor_set(v___x_3306_, 3, v_l_3585_);
lean_ctor_set(v___x_3306_, 2, v_v_3589_);
lean_ctor_set(v___x_3306_, 1, v_k_3588_);
lean_ctor_set(v___x_3306_, 0, v___x_3595_);
v___x_3600_ = v___x_3306_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_k_3588_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_v_3589_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_k_3606_; lean_object* v_v_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3619_; 
v_k_3606_ = lean_ctor_get(v___x_3486_, 1);
v_v_3607_ = lean_ctor_get(v___x_3486_, 2);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; 
v_unused_3620_ = lean_ctor_get(v___x_3486_, 4);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v___x_3486_, 3);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v___x_3486_, 0);
lean_dec(v_unused_3622_);
v___x_3609_ = v___x_3486_;
v_isShared_3610_ = v_isSharedCheck_3619_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_v_3607_);
lean_inc(v_k_3606_);
lean_dec(v___x_3486_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3619_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3611_ = lean_unsigned_to_nat(3u);
v___x_3612_ = lean_unsigned_to_nat(1u);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 3, v_r_3586_);
lean_ctor_set(v___x_3609_, 2, v_v_3302_);
lean_ctor_set(v___x_3609_, 1, v_k_3301_);
lean_ctor_set(v___x_3609_, 0, v___x_3612_);
v___x_3614_ = v___x_3609_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_r_3586_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v_r_3586_);
v___x_3614_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3614_);
lean_ctor_set(v___x_3306_, 3, v_l_3585_);
lean_ctor_set(v___x_3306_, 2, v_v_3607_);
lean_ctor_set(v___x_3306_, 1, v_k_3606_);
lean_ctor_set(v___x_3306_, 0, v___x_3611_);
v___x_3616_ = v___x_3306_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_k_3606_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_v_3607_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
else
{
lean_object* v_r_3623_; 
v_r_3623_ = lean_ctor_get(v___x_3486_, 4);
lean_inc(v_r_3623_);
if (lean_obj_tag(v_r_3623_) == 0)
{
lean_object* v_k_3624_; lean_object* v_v_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3649_; 
v_k_3624_ = lean_ctor_get(v___x_3486_, 1);
v_v_3625_ = lean_ctor_get(v___x_3486_, 2);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; lean_object* v_unused_3651_; lean_object* v_unused_3652_; 
v_unused_3650_ = lean_ctor_get(v___x_3486_, 4);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v___x_3486_, 3);
lean_dec(v_unused_3651_);
v_unused_3652_ = lean_ctor_get(v___x_3486_, 0);
lean_dec(v_unused_3652_);
v___x_3627_ = v___x_3486_;
v_isShared_3628_ = v_isSharedCheck_3649_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_v_3625_);
lean_inc(v_k_3624_);
lean_dec(v___x_3486_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3649_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_k_3629_; lean_object* v_v_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3645_; 
v_k_3629_ = lean_ctor_get(v_r_3623_, 1);
v_v_3630_ = lean_ctor_get(v_r_3623_, 2);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_r_3623_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; lean_object* v_unused_3647_; lean_object* v_unused_3648_; 
v_unused_3646_ = lean_ctor_get(v_r_3623_, 4);
lean_dec(v_unused_3646_);
v_unused_3647_ = lean_ctor_get(v_r_3623_, 3);
lean_dec(v_unused_3647_);
v_unused_3648_ = lean_ctor_get(v_r_3623_, 0);
lean_dec(v_unused_3648_);
v___x_3632_ = v_r_3623_;
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_v_3630_);
lean_inc(v_k_3629_);
lean_dec(v_r_3623_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3634_ = lean_unsigned_to_nat(3u);
v___x_3635_ = lean_unsigned_to_nat(1u);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 4, v_l_3585_);
lean_ctor_set(v___x_3632_, 3, v_l_3585_);
lean_ctor_set(v___x_3632_, 2, v_v_3625_);
lean_ctor_set(v___x_3632_, 1, v_k_3624_);
lean_ctor_set(v___x_3632_, 0, v___x_3635_);
v___x_3637_ = v___x_3632_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3624_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3625_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_l_3585_);
v___x_3637_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 4, v_l_3585_);
lean_ctor_set(v___x_3627_, 2, v_v_3302_);
lean_ctor_set(v___x_3627_, 1, v_k_3301_);
lean_ctor_set(v___x_3627_, 0, v___x_3635_);
v___x_3639_ = v___x_3627_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_l_3585_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3639_);
lean_ctor_set(v___x_3306_, 3, v___x_3637_);
lean_ctor_set(v___x_3306_, 2, v_v_3630_);
lean_ctor_set(v___x_3306_, 1, v_k_3629_);
lean_ctor_set(v___x_3306_, 0, v___x_3634_);
v___x_3641_ = v___x_3306_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_k_3629_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_v_3630_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = lean_unsigned_to_nat(2u);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_r_3623_);
lean_ctor_set(v___x_3306_, 3, v___x_3486_);
lean_ctor_set(v___x_3306_, 0, v___x_3653_);
v___x_3655_ = v___x_3306_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v_r_3623_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3657_ = lean_unsigned_to_nat(1u);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3486_);
lean_ctor_set(v___x_3306_, 3, v___x_3486_);
lean_ctor_set(v___x_3306_, 0, v___x_3657_);
v___x_3659_ = v___x_3306_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v___x_3486_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_ctor_set(v___x_3663_, 1, v_k_3297_);
lean_ctor_set(v___x_3663_, 2, v_v_3298_);
lean_ctor_set(v___x_3663_, 3, v_t_3299_);
lean_ctor_set(v___x_3663_, 4, v_t_3299_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(lean_object* v_init_3664_, lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 0)
{
lean_object* v_k_3666_; lean_object* v_v_3667_; lean_object* v_l_3668_; lean_object* v_r_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_k_3666_ = lean_ctor_get(v_x_3665_, 1);
lean_inc(v_k_3666_);
v_v_3667_ = lean_ctor_get(v_x_3665_, 2);
lean_inc(v_v_3667_);
v_l_3668_ = lean_ctor_get(v_x_3665_, 3);
lean_inc(v_l_3668_);
v_r_3669_ = lean_ctor_get(v_x_3665_, 4);
lean_inc(v_r_3669_);
lean_dec_ref(v_x_3665_);
v___x_3670_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(v_init_3664_, v_l_3668_);
v___x_3671_ = 1;
v___x_3672_ = l_Lean_Name_toString(v_k_3666_, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_v_3667_);
v___x_3674_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v___x_3672_, v___x_3673_, v___x_3670_);
v_init_3664_ = v___x_3674_;
v_x_3665_ = v_r_3669_;
goto _start;
}
else
{
return v_init_3664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3676_){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_box(1);
v___x_3678_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(v___x_3677_, v_m_3676_);
v___x_3679_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3682_, uint8_t v_updateToolchain_3683_, lean_object* v_ws_3684_, lean_object* v_dep_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_baseName_3689_; lean_object* v_name_3690_; lean_object* v_opts_3691_; uint8_t v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_baseName_3689_ = lean_ctor_get(v___x_3682_, 1);
v_name_3690_ = lean_ctor_get(v_dep_3685_, 0);
v_opts_3691_ = lean_ctor_get(v_dep_3685_, 4);
v___x_3692_ = 0;
lean_inc(v_baseName_3689_);
v___x_3693_ = l_Lean_Name_toString(v_baseName_3689_, v___x_3692_);
v___x_3694_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3695_ = lean_string_append(v___x_3693_, v___x_3694_);
lean_inc(v_name_3690_);
v___x_3696_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3690_, v_updateToolchain_3683_);
v___x_3697_ = lean_string_append(v___x_3695_, v___x_3696_);
lean_dec_ref(v___x_3696_);
v___x_3698_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3699_ = lean_string_append(v___x_3697_, v___x_3698_);
lean_inc(v_opts_3691_);
v___x_3700_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3691_);
v___x_3701_ = lean_unsigned_to_nat(80u);
v___x_3702_ = l_Lean_Json_pretty(v___x_3700_, v___x_3701_);
v___x_3703_ = lean_string_append(v___x_3699_, v___x_3702_);
lean_dec_ref(v___x_3702_);
v___x_3704_ = 0;
v___x_3705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*1, v___x_3704_);
lean_inc_ref(v___y_3687_);
v___x_3706_ = lean_apply_2(v___y_3687_, v___x_3705_, lean_box(0));
v___x_3707_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3684_, v___x_3682_, v_dep_3685_, v___y_3686_, v___y_3687_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3708_, lean_object* v_updateToolchain_3709_, lean_object* v_ws_3710_, lean_object* v_dep_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v_updateToolchain_boxed_3715_; lean_object* v_res_3716_; 
v_updateToolchain_boxed_3715_ = lean_unbox(v_updateToolchain_3709_);
v_res_3716_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3708_, v_updateToolchain_boxed_3715_, v_ws_3710_, v_dep_3711_, v___y_3712_, v___y_3713_);
lean_dec_ref(v___y_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_val_3717_, size_t v_sz_3718_, size_t v_i_3719_, lean_object* v_bs_3720_){
_start:
{
uint8_t v___x_3721_; 
v___x_3721_ = lean_usize_dec_lt(v_i_3719_, v_sz_3718_);
if (v___x_3721_ == 0)
{
return v_bs_3720_;
}
else
{
lean_object* v_packages_3722_; lean_object* v_v_3723_; lean_object* v___x_3724_; lean_object* v_bs_x27_3725_; lean_object* v___x_3726_; size_t v___x_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v_packages_3722_ = lean_ctor_get(v_val_3717_, 4);
v_v_3723_ = lean_array_uget(v_bs_3720_, v_i_3719_);
v___x_3724_ = lean_unsigned_to_nat(0u);
v_bs_x27_3725_ = lean_array_uset(v_bs_3720_, v_i_3719_, v___x_3724_);
v___x_3726_ = lean_array_fget_borrowed(v_packages_3722_, v_v_3723_);
lean_dec(v_v_3723_);
v___x_3727_ = ((size_t)1ULL);
v___x_3728_ = lean_usize_add(v_i_3719_, v___x_3727_);
lean_inc(v___x_3726_);
v___x_3729_ = lean_array_uset(v_bs_x27_3725_, v_i_3719_, v___x_3726_);
v_i_3719_ = v___x_3728_;
v_bs_3720_ = v___x_3729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_val_3731_, lean_object* v_sz_3732_, lean_object* v_i_3733_, lean_object* v_bs_3734_){
_start:
{
size_t v_sz_boxed_3735_; size_t v_i_boxed_3736_; lean_object* v_res_3737_; 
v_sz_boxed_3735_ = lean_unbox_usize(v_sz_3732_);
lean_dec(v_sz_3732_);
v_i_boxed_3736_ = lean_unbox_usize(v_i_3733_);
lean_dec(v_i_3733_);
v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_val_3731_, v_sz_boxed_3735_, v_i_boxed_3736_, v_bs_3734_);
lean_dec_ref(v_val_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0(lean_object* v___x_3738_, lean_object* v_x_3739_){
_start:
{
lean_object* v_baseName_3740_; lean_object* v_name_3741_; uint8_t v___x_3742_; 
v_baseName_3740_ = lean_ctor_get(v_x_3739_, 1);
v_name_3741_ = lean_ctor_get(v___x_3738_, 0);
v___x_3742_ = lean_name_eq(v_baseName_3740_, v_name_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed(lean_object* v___x_3743_, lean_object* v_x_3744_){
_start:
{
uint8_t v_res_3745_; lean_object* v_r_3746_; 
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0(v___x_3743_, v_x_3744_);
lean_dec_ref(v_x_3744_);
lean_dec_ref(v___x_3743_);
v_r_3746_ = lean_box(v_res_3745_);
return v_r_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(lean_object* v_pkg_3747_, lean_object* v_leanOpts_3748_, uint8_t v_reconfigure_3749_, lean_object* v_as_3750_, size_t v_i_3751_, size_t v_stop_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_usize_dec_eq(v_i_3751_, v_stop_3752_);
if (v___x_3760_ == 0)
{
lean_object* v_ws_3761_; lean_object* v_depIdxs_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3877_; 
v_ws_3761_ = lean_ctor_get(v_b_3753_, 0);
v_depIdxs_3762_ = lean_ctor_get(v_b_3753_, 1);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_b_3753_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3764_ = v_b_3753_;
v_isShared_3765_ = v_isSharedCheck_3877_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_depIdxs_3762_);
lean_inc(v_ws_3761_);
lean_dec(v_b_3753_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3877_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_packages_3766_; size_t v___x_3767_; size_t v___x_3768_; lean_object* v___x_3769_; lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_packages_3766_ = lean_ctor_get(v_ws_3761_, 4);
v___x_3767_ = ((size_t)1ULL);
v___x_3768_ = lean_usize_sub(v_i_3751_, v___x_3767_);
v___x_3769_ = lean_array_uget_borrowed(v_as_3750_, v___x_3768_);
lean_inc(v___x_3769_);
v___f_3770_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3770_, 0, v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(0u);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3770_, v_packages_3766_, v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 1)
{
lean_object* v_val_3773_; lean_object* v___x_3774_; lean_object* v___x_3776_; 
v_val_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_val_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_array_push(v_depIdxs_3762_, v_val_3773_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v___x_3774_);
v___x_3776_ = v___x_3764_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_ws_3761_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
v_i_3751_ = v___x_3768_;
v_b_3753_ = v___x_3776_;
goto _start;
}
}
else
{
lean_object* v_baseName_3779_; lean_object* v_name_3780_; lean_object* v_opts_3781_; uint8_t v___x_3782_; 
lean_inc_ref(v_packages_3766_);
lean_dec(v___x_3772_);
v_baseName_3779_ = lean_ctor_get(v_pkg_3747_, 1);
v_name_3780_ = lean_ctor_get(v___x_3769_, 0);
v_opts_3781_ = lean_ctor_get(v___x_3769_, 4);
v___x_3782_ = lean_name_eq(v_baseName_3779_, v_name_3780_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; 
lean_inc_ref(v___y_3755_);
lean_inc_ref(v_ws_3761_);
lean_inc(v___x_3769_);
lean_inc_ref(v_pkg_3747_);
v___x_3783_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3747_, v___x_3769_, v_ws_3761_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3860_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3786_ = v___x_3783_;
v_isShared_3787_ = v_isSharedCheck_3860_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3860_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v_fst_3788_; lean_object* v_snd_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_fst_3788_ = lean_ctor_get(v_a_3784_, 0);
lean_inc(v_fst_3788_);
v_snd_3789_ = lean_ctor_get(v_a_3784_, 1);
lean_inc(v_snd_3789_);
lean_dec(v_a_3784_);
v___x_3790_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3748_);
lean_inc(v_opts_3781_);
v___x_3791_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_3761_, v_fst_3788_, v_opts_3781_, v_leanOpts_3748_, v_reconfigure_3749_, v___x_3790_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v_a_3793_; lean_object* v_wsIdx_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
lean_del_object(v___x_3786_);
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
v_a_3793_ = lean_ctor_get(v___x_3791_, 1);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3791_);
v_wsIdx_3794_ = lean_array_get_size(v_packages_3766_);
lean_dec_ref(v_packages_3766_);
v___x_3795_ = lean_array_push(v_depIdxs_3762_, v_wsIdx_3794_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v___x_3795_);
lean_ctor_set(v___x_3764_, 0, v_a_3792_);
v___x_3797_ = v___x_3764_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3792_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = lean_array_get_size(v_a_3793_);
v___x_3799_ = lean_nat_dec_lt(v___x_3771_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_dec(v_a_3793_);
v_i_3751_ = v___x_3768_;
v_b_3753_ = v___x_3797_;
v___y_3754_ = v_snd_3789_;
goto _start;
}
else
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3801_ = lean_box(0);
v___x_3802_ = lean_nat_dec_le(v___x_3798_, v___x_3798_);
if (v___x_3802_ == 0)
{
if (v___x_3799_ == 0)
{
lean_dec(v_a_3793_);
v_i_3751_ = v___x_3768_;
v_b_3753_ = v___x_3797_;
v___y_3754_ = v_snd_3789_;
goto _start;
}
else
{
size_t v___x_3804_; size_t v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((size_t)0ULL);
v___x_3805_ = lean_usize_of_nat(v___x_3798_);
v___x_3806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3793_, v___x_3804_, v___x_3805_, v___x_3801_, v___y_3755_);
lean_dec(v_a_3793_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref(v___x_3806_);
v_i_3751_ = v___x_3768_;
v_b_3753_ = v___x_3797_;
v___y_3754_ = v_snd_3789_;
goto _start;
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___x_3797_);
lean_dec(v_snd_3789_);
lean_dec_ref(v_leanOpts_3748_);
lean_dec_ref(v_pkg_3747_);
v_a_3808_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3806_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
else
{
size_t v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((size_t)0ULL);
v___x_3817_ = lean_usize_of_nat(v___x_3798_);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3793_, v___x_3816_, v___x_3817_, v___x_3801_, v___y_3755_);
lean_dec(v_a_3793_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_dec_ref(v___x_3818_);
v_i_3751_ = v___x_3768_;
v_b_3753_ = v___x_3797_;
v___y_3754_ = v_snd_3789_;
goto _start;
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v___x_3797_);
lean_dec(v_snd_3789_);
lean_dec_ref(v_leanOpts_3748_);
lean_dec_ref(v_pkg_3747_);
v_a_3820_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3818_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3818_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
lean_dec(v_snd_3789_);
lean_dec_ref(v_packages_3766_);
lean_del_object(v___x_3764_);
lean_dec_ref(v_depIdxs_3762_);
lean_dec_ref(v_leanOpts_3748_);
lean_dec_ref(v_pkg_3747_);
v_a_3829_ = lean_ctor_get(v___x_3791_, 1);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3791_);
v___x_3830_ = lean_array_get_size(v_a_3829_);
v___x_3831_ = lean_nat_dec_lt(v___x_3771_, v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_a_3829_);
v___x_3832_ = lean_box(0);
if (v_isShared_3787_ == 0)
{
lean_ctor_set_tag(v___x_3786_, 1);
lean_ctor_set(v___x_3786_, 0, v___x_3832_);
v___x_3834_ = v___x_3786_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
else
{
lean_object* v___x_3836_; uint8_t v___x_3837_; 
lean_del_object(v___x_3786_);
v___x_3836_ = lean_box(0);
v___x_3837_ = lean_nat_dec_le(v___x_3830_, v___x_3830_);
if (v___x_3837_ == 0)
{
if (v___x_3831_ == 0)
{
lean_dec(v_a_3829_);
goto v___jp_3757_;
}
else
{
size_t v___x_3838_; size_t v___x_3839_; lean_object* v___x_3840_; 
v___x_3838_ = ((size_t)0ULL);
v___x_3839_ = lean_usize_of_nat(v___x_3830_);
v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3829_, v___x_3838_, v___x_3839_, v___x_3836_, v___y_3755_);
lean_dec(v_a_3829_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_dec_ref(v___x_3840_);
goto v___jp_3757_;
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
size_t v___x_3849_; size_t v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = ((size_t)0ULL);
v___x_3850_ = lean_usize_of_nat(v___x_3830_);
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3829_, v___x_3849_, v___x_3850_, v___x_3836_, v___y_3755_);
lean_dec(v_a_3829_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_dec_ref(v___x_3851_);
goto v___jp_3757_;
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
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
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_packages_3766_);
lean_del_object(v___x_3764_);
lean_dec_ref(v_depIdxs_3762_);
lean_dec_ref(v_ws_3761_);
lean_dec_ref(v_leanOpts_3748_);
lean_dec_ref(v_pkg_3747_);
v_a_3861_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3783_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3783_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_inc(v_baseName_3779_);
lean_dec_ref(v_packages_3766_);
lean_del_object(v___x_3764_);
lean_dec_ref(v_depIdxs_3762_);
lean_dec_ref(v_ws_3761_);
lean_dec(v___y_3754_);
lean_dec_ref(v_leanOpts_3748_);
lean_dec_ref(v_pkg_3747_);
v___x_3869_ = l_Lean_Name_toString(v_baseName_3779_, v___x_3760_);
v___x_3870_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_3871_ = lean_string_append(v___x_3869_, v___x_3870_);
v___x_3872_ = 3;
v___x_3873_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set_uint8(v___x_3873_, sizeof(void*)*1, v___x_3872_);
lean_inc_ref(v___y_3755_);
v___x_3874_ = lean_apply_2(v___y_3755_, v___x_3873_, lean_box(0));
v___x_3875_ = lean_box(0);
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
return v___x_3876_;
}
}
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec_ref(v_leanOpts_3748_);
lean_dec_ref(v_pkg_3747_);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v_b_3753_);
lean_ctor_set(v___x_3878_, 1, v___y_3754_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
v___jp_3757_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = lean_box(0);
v___x_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___boxed(lean_object* v_pkg_3880_, lean_object* v_leanOpts_3881_, lean_object* v_reconfigure_3882_, lean_object* v_as_3883_, lean_object* v_i_3884_, lean_object* v_stop_3885_, lean_object* v_b_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
uint8_t v_reconfigure_boxed_3890_; size_t v_i_boxed_3891_; size_t v_stop_boxed_3892_; lean_object* v_res_3893_; 
v_reconfigure_boxed_3890_ = lean_unbox(v_reconfigure_3882_);
v_i_boxed_3891_ = lean_unbox_usize(v_i_3884_);
lean_dec(v_i_3884_);
v_stop_boxed_3892_ = lean_unbox_usize(v_stop_3885_);
lean_dec(v_stop_3885_);
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3880_, v_leanOpts_3881_, v_reconfigure_boxed_3890_, v_as_3883_, v_i_boxed_3891_, v_stop_boxed_3892_, v_b_3886_, v___y_3887_, v___y_3888_);
lean_dec_ref(v___y_3888_);
lean_dec_ref(v_as_3883_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_3894_, uint8_t v_reconfigure_3895_, lean_object* v_ws_3896_, lean_object* v_wsIdx_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_packages_3901_; lean_object* v_pkg_3902_; lean_object* v_depConfigs_3903_; lean_object* v_start_3904_; lean_object* v_ws_3906_; lean_object* v_packages_3907_; lean_object* v_depIdxs_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v_____x_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v_s_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v_packages_3901_ = lean_ctor_get(v_ws_3896_, 4);
v_pkg_3902_ = lean_array_fget(v_packages_3901_, v_wsIdx_3897_);
v_depConfigs_3903_ = lean_ctor_get(v_pkg_3902_, 12);
v_start_3904_ = lean_array_get_size(v_packages_3901_);
v___x_3941_ = lean_array_get_size(v_depConfigs_3903_);
v___x_3942_ = lean_mk_empty_array_with_capacity(v___x_3941_);
lean_inc_ref(v___x_3942_);
lean_inc_ref(v_ws_3896_);
v_s_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_3943_, 0, v_ws_3896_);
lean_ctor_set(v_s_3943_, 1, v___x_3942_);
v___x_3944_ = lean_unsigned_to_nat(0u);
v___x_3945_ = lean_nat_dec_le(v___x_3941_, v___x_3941_);
if (v___x_3945_ == 0)
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3941_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_dec_ref(v_s_3943_);
v___x_3947_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_start_3904_, v_leanOpts_3894_, v_reconfigure_3895_, v_start_3904_, v_ws_3896_, v___y_3898_, v___y_3899_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3968_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3950_ = v___x_3947_;
v_isShared_3951_ = v_isSharedCheck_3968_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3947_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3968_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v_fst_3952_; lean_object* v_snd_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3967_; 
v_fst_3952_ = lean_ctor_get(v_a_3948_, 0);
v_snd_3953_ = lean_ctor_get(v_a_3948_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_a_3948_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3955_ = v_a_3948_;
v_isShared_3956_ = v_isSharedCheck_3967_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_snd_3953_);
lean_inc(v_fst_3952_);
lean_dec(v_a_3948_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3967_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
size_t v_sz_3957_; size_t v___x_3958_; lean_object* v_depPkgs_3959_; lean_object* v_ws_3960_; lean_object* v___x_3962_; 
v_sz_3957_ = lean_array_size(v___x_3942_);
v___x_3958_ = ((size_t)0ULL);
v_depPkgs_3959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_fst_3952_, v_sz_3957_, v___x_3958_, v___x_3942_);
v_ws_3960_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_3952_, v_pkg_3902_, v_depPkgs_3959_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v_ws_3960_);
v___x_3962_ = v___x_3955_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_ws_3960_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_snd_3953_);
v___x_3962_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3964_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v___x_3962_);
v___x_3964_ = v___x_3950_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3942_);
lean_dec(v_pkg_3902_);
return v___x_3947_;
}
}
else
{
size_t v___x_3969_; size_t v___x_3970_; lean_object* v___x_3971_; 
lean_dec_ref(v___x_3942_);
lean_dec_ref(v_ws_3896_);
v___x_3969_ = lean_usize_of_nat(v___x_3941_);
v___x_3970_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_3894_);
lean_inc(v_pkg_3902_);
v___x_3971_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3902_, v_leanOpts_3894_, v_reconfigure_3895_, v_depConfigs_3903_, v___x_3969_, v___x_3970_, v_s_3943_, v___y_3898_, v___y_3899_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v_fst_3973_; lean_object* v_snd_3974_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref(v___x_3971_);
v_fst_3973_ = lean_ctor_get(v_a_3972_, 0);
lean_inc(v_fst_3973_);
v_snd_3974_ = lean_ctor_get(v_a_3972_, 1);
lean_inc(v_snd_3974_);
lean_dec(v_a_3972_);
v_____x_3935_ = v_fst_3973_;
v___y_3936_ = v_snd_3974_;
v___y_3937_ = v___y_3899_;
goto v___jp_3934_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_pkg_3902_);
lean_dec_ref(v_leanOpts_3894_);
v_a_3975_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3971_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3971_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
else
{
uint8_t v___x_3983_; 
lean_inc_ref(v_packages_3901_);
v___x_3983_ = lean_nat_dec_lt(v___x_3944_, v___x_3941_);
if (v___x_3983_ == 0)
{
lean_dec_ref(v_s_3943_);
v_ws_3906_ = v_ws_3896_;
v_packages_3907_ = v_packages_3901_;
v_depIdxs_3908_ = v___x_3942_;
v___y_3909_ = v___y_3898_;
v___y_3910_ = v___y_3899_;
goto v___jp_3905_;
}
else
{
size_t v___x_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
lean_dec_ref(v___x_3942_);
lean_dec_ref(v_packages_3901_);
lean_dec_ref(v_ws_3896_);
v___x_3984_ = lean_usize_of_nat(v___x_3941_);
v___x_3985_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_3894_);
lean_inc(v_pkg_3902_);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3902_, v_leanOpts_3894_, v_reconfigure_3895_, v_depConfigs_3903_, v___x_3984_, v___x_3985_, v_s_3943_, v___y_3898_, v___y_3899_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v_fst_3988_; lean_object* v_snd_3989_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref(v___x_3986_);
v_fst_3988_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_fst_3988_);
v_snd_3989_ = lean_ctor_get(v_a_3987_, 1);
lean_inc(v_snd_3989_);
lean_dec(v_a_3987_);
v_____x_3935_ = v_fst_3988_;
v___y_3936_ = v_snd_3989_;
v___y_3937_ = v___y_3899_;
goto v___jp_3934_;
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_pkg_3902_);
lean_dec_ref(v_leanOpts_3894_);
v_a_3990_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3986_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3986_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
v___jp_3905_:
{
lean_object* v_stop_3911_; lean_object* v___x_3912_; 
v_stop_3911_ = lean_array_get_size(v_packages_3907_);
lean_dec_ref(v_packages_3907_);
v___x_3912_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_stop_3911_, v_leanOpts_3894_, v_reconfigure_3895_, v_start_3904_, v_ws_3906_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3933_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3933_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3933_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v_fst_3917_; lean_object* v_snd_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3932_; 
v_fst_3917_ = lean_ctor_get(v_a_3913_, 0);
v_snd_3918_ = lean_ctor_get(v_a_3913_, 1);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_a_3913_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3920_ = v_a_3913_;
v_isShared_3921_ = v_isSharedCheck_3932_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_snd_3918_);
lean_inc(v_fst_3917_);
lean_dec(v_a_3913_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3932_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
size_t v_sz_3922_; size_t v___x_3923_; lean_object* v_depPkgs_3924_; lean_object* v_ws_3925_; lean_object* v___x_3927_; 
v_sz_3922_ = lean_array_size(v_depIdxs_3908_);
v___x_3923_ = ((size_t)0ULL);
v_depPkgs_3924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_fst_3917_, v_sz_3922_, v___x_3923_, v_depIdxs_3908_);
v_ws_3925_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_3917_, v_pkg_3902_, v_depPkgs_3924_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v_ws_3925_);
v___x_3927_ = v___x_3920_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_ws_3925_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_snd_3918_);
v___x_3927_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3929_; 
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3927_);
v___x_3929_ = v___x_3915_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
else
{
lean_dec_ref(v_depIdxs_3908_);
lean_dec(v_pkg_3902_);
return v___x_3912_;
}
}
v___jp_3934_:
{
lean_object* v_ws_3938_; lean_object* v_depIdxs_3939_; lean_object* v_packages_3940_; 
v_ws_3938_ = lean_ctor_get(v_____x_3935_, 0);
lean_inc_ref(v_ws_3938_);
v_depIdxs_3939_ = lean_ctor_get(v_____x_3935_, 1);
lean_inc_ref(v_depIdxs_3939_);
lean_dec_ref(v_____x_3935_);
v_packages_3940_ = lean_ctor_get(v_ws_3938_, 4);
lean_inc_ref(v_packages_3940_);
v_ws_3906_ = v_ws_3938_;
v_packages_3907_ = v_packages_3940_;
v_depIdxs_3908_ = v_depIdxs_3939_;
v___y_3909_ = v___y_3936_;
v___y_3910_ = v___y_3937_;
goto v___jp_3905_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(lean_object* v_upperBound_3998_, lean_object* v_leanOpts_3999_, uint8_t v_reconfigure_4000_, lean_object* v_a_4001_, lean_object* v_b_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
uint8_t v___x_4006_; 
v___x_4006_ = lean_nat_dec_lt(v_a_4001_, v_upperBound_3998_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_dec(v_a_4001_);
lean_dec_ref(v_leanOpts_3999_);
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v_b_4002_);
lean_ctor_set(v___x_4007_, 1, v___y_4003_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
else
{
lean_object* v___x_4009_; 
lean_inc_ref(v_leanOpts_3999_);
v___x_4009_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_3999_, v_reconfigure_4000_, v_b_4002_, v_a_4001_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v_fst_4011_; lean_object* v_snd_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref(v___x_4009_);
v_fst_4011_ = lean_ctor_get(v_a_4010_, 0);
lean_inc(v_fst_4011_);
v_snd_4012_ = lean_ctor_get(v_a_4010_, 1);
lean_inc(v_snd_4012_);
lean_dec(v_a_4010_);
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_add(v_a_4001_, v___x_4013_);
lean_dec(v_a_4001_);
v_a_4001_ = v___x_4014_;
v_b_4002_ = v_fst_4011_;
v___y_4003_ = v_snd_4012_;
goto _start;
}
else
{
lean_dec(v_a_4001_);
lean_dec_ref(v_leanOpts_3999_);
return v___x_4009_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg___boxed(lean_object* v_upperBound_4016_, lean_object* v_leanOpts_4017_, lean_object* v_reconfigure_4018_, lean_object* v_a_4019_, lean_object* v_b_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
uint8_t v_reconfigure_boxed_4024_; lean_object* v_res_4025_; 
v_reconfigure_boxed_4024_ = lean_unbox(v_reconfigure_4018_);
v_res_4025_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_upperBound_4016_, v_leanOpts_4017_, v_reconfigure_boxed_4024_, v_a_4019_, v_b_4020_, v___y_4021_, v___y_4022_);
lean_dec_ref(v___y_4022_);
lean_dec(v_upperBound_4016_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4026_, lean_object* v_reconfigure_4027_, lean_object* v_ws_4028_, lean_object* v_wsIdx_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
uint8_t v_reconfigure_boxed_4033_; lean_object* v_res_4034_; 
v_reconfigure_boxed_4033_ = lean_unbox(v_reconfigure_4027_);
v_res_4034_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4026_, v_reconfigure_boxed_4033_, v_ws_4028_, v_wsIdx_4029_, v___y_4030_, v___y_4031_);
lean_dec_ref(v___y_4031_);
lean_dec(v_wsIdx_4029_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_upperBound_4035_, lean_object* v_leanOpts_4036_, lean_object* v_a_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
uint8_t v___x_4042_; 
v___x_4042_ = lean_nat_dec_lt(v_a_4037_, v_upperBound_4035_);
if (v___x_4042_ == 0)
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
lean_dec(v_a_4037_);
lean_dec_ref(v_leanOpts_4036_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v_b_4038_);
lean_ctor_set(v___x_4043_, 1, v___y_4039_);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
else
{
lean_object* v___x_4045_; 
lean_inc_ref(v_leanOpts_4036_);
v___x_4045_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4036_, v___x_4042_, v_b_4038_, v_a_4037_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v_fst_4047_; lean_object* v_snd_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref(v___x_4045_);
v_fst_4047_ = lean_ctor_get(v_a_4046_, 0);
lean_inc(v_fst_4047_);
v_snd_4048_ = lean_ctor_get(v_a_4046_, 1);
lean_inc(v_snd_4048_);
lean_dec(v_a_4046_);
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_nat_add(v_a_4037_, v___x_4049_);
lean_dec(v_a_4037_);
v_a_4037_ = v___x_4050_;
v_b_4038_ = v_fst_4047_;
v___y_4039_ = v_snd_4048_;
goto _start;
}
else
{
lean_dec(v_a_4037_);
lean_dec_ref(v_leanOpts_4036_);
return v___x_4045_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg___boxed(lean_object* v_upperBound_4052_, lean_object* v_leanOpts_4053_, lean_object* v_a_4054_, lean_object* v_b_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_upperBound_4052_, v_leanOpts_4053_, v_a_4054_, v_b_4055_, v___y_4056_, v___y_4057_);
lean_dec_ref(v___y_4057_);
lean_dec(v_upperBound_4052_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_4060_, lean_object* v_f_4061_, lean_object* v_xs_4062_, lean_object* v_k_4063_, lean_object* v_acc_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
uint8_t v___x_4068_; 
v___x_4068_ = lean_nat_dec_lt(v_k_4063_, v_n_4060_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec(v_k_4063_);
lean_dec_ref(v_f_4061_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v_acc_4064_);
lean_ctor_set(v___x_4069_, 1, v___y_4065_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
return v___x_4070_;
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_array_fget_borrowed(v_xs_4062_, v_k_4063_);
lean_inc_ref(v_f_4061_);
lean_inc_ref(v___y_4066_);
lean_inc(v___x_4071_);
v___x_4072_ = lean_apply_4(v_f_4061_, v___x_4071_, v___y_4065_, v___y_4066_, lean_box(0));
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v_fst_4074_; lean_object* v_snd_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref(v___x_4072_);
v_fst_4074_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_fst_4074_);
v_snd_4075_ = lean_ctor_get(v_a_4073_, 1);
lean_inc(v_snd_4075_);
lean_dec(v_a_4073_);
v___x_4076_ = lean_unsigned_to_nat(1u);
v___x_4077_ = lean_nat_add(v_k_4063_, v___x_4076_);
lean_dec(v_k_4063_);
v___x_4078_ = lean_array_push(v_acc_4064_, v_fst_4074_);
v_k_4063_ = v___x_4077_;
v_acc_4064_ = v___x_4078_;
v___y_4065_ = v_snd_4075_;
goto _start;
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
lean_dec_ref(v_acc_4064_);
lean_dec(v_k_4063_);
lean_dec_ref(v_f_4061_);
v_a_4080_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4072_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4072_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_4088_, lean_object* v_f_4089_, lean_object* v_xs_4090_, lean_object* v_k_4091_, lean_object* v_acc_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4088_, v_f_4089_, v_xs_4090_, v_k_4091_, v_acc_4092_, v___y_4093_, v___y_4094_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v_xs_4090_);
lean_dec(v_n_4088_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_4097_, lean_object* v_fst_4098_, lean_object* v___x_4099_, lean_object* v_leanOpts_4100_, lean_object* v_a_4101_, lean_object* v_b_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v___x_4109_; 
v___x_4109_ = lean_nat_dec_lt(v_a_4101_, v_upperBound_4097_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec(v_a_4101_);
lean_dec_ref(v_leanOpts_4100_);
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v_b_4102_);
lean_ctor_set(v___x_4110_, 1, v___y_4103_);
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
return v___x_4111_;
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_array_fget_borrowed(v_fst_4098_, v_a_4101_);
lean_inc(v___x_4112_);
v___x_4113_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_4112_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4188_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4188_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4188_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v_snd_4118_; lean_object* v___x_4119_; lean_object* v_opts_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_snd_4118_ = lean_ctor_get(v_a_4114_, 1);
lean_inc(v_snd_4118_);
lean_dec(v_a_4114_);
v___x_4119_ = lean_array_fget_borrowed(v___x_4099_, v_a_4101_);
v_opts_4120_ = lean_ctor_get(v___x_4119_, 4);
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4100_);
lean_inc(v_opts_4120_);
lean_inc(v___x_4112_);
v___x_4123_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_4102_, v___x_4112_, v_opts_4120_, v_leanOpts_4100_, v___x_4109_, v___x_4122_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v_a_4125_; lean_object* v_snd_4127_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
lean_del_object(v___x_4116_);
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
v_a_4125_ = lean_ctor_get(v___x_4123_, 1);
lean_inc(v_a_4125_);
lean_dec_ref(v___x_4123_);
v___x_4131_ = lean_array_get_size(v_a_4125_);
v___x_4132_ = lean_nat_dec_lt(v___x_4121_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_dec(v_a_4125_);
v_snd_4127_ = v_snd_4118_;
goto v___jp_4126_;
}
else
{
lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4133_ = lean_box(0);
v___x_4134_ = lean_nat_dec_le(v___x_4131_, v___x_4131_);
if (v___x_4134_ == 0)
{
if (v___x_4132_ == 0)
{
lean_dec(v_a_4125_);
v_snd_4127_ = v_snd_4118_;
goto v___jp_4126_;
}
else
{
size_t v___x_4135_; size_t v___x_4136_; lean_object* v___x_4137_; 
v___x_4135_ = ((size_t)0ULL);
v___x_4136_ = lean_usize_of_nat(v___x_4131_);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4125_, v___x_4135_, v___x_4136_, v___x_4133_, v___y_4104_);
lean_dec(v_a_4125_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_dec_ref(v___x_4137_);
v_snd_4127_ = v_snd_4118_;
goto v___jp_4126_;
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v_a_4124_);
lean_dec(v_snd_4118_);
lean_dec(v_a_4101_);
lean_dec_ref(v_leanOpts_4100_);
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
else
{
size_t v___x_4146_; size_t v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = ((size_t)0ULL);
v___x_4147_ = lean_usize_of_nat(v___x_4131_);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4125_, v___x_4146_, v___x_4147_, v___x_4133_, v___y_4104_);
lean_dec(v_a_4125_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_dec_ref(v___x_4148_);
v_snd_4127_ = v_snd_4118_;
goto v___jp_4126_;
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec(v_a_4124_);
lean_dec(v_snd_4118_);
lean_dec(v_a_4101_);
lean_dec_ref(v_leanOpts_4100_);
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
v___jp_4126_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_unsigned_to_nat(1u);
v___x_4129_ = lean_nat_add(v_a_4101_, v___x_4128_);
lean_dec(v_a_4101_);
v_a_4101_ = v___x_4129_;
v_b_4102_ = v_a_4124_;
v___y_4103_ = v_snd_4127_;
goto _start;
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; 
lean_dec(v_snd_4118_);
lean_dec(v_a_4101_);
lean_dec_ref(v_leanOpts_4100_);
v_a_4157_ = lean_ctor_get(v___x_4123_, 1);
lean_inc(v_a_4157_);
lean_dec_ref(v___x_4123_);
v___x_4158_ = lean_array_get_size(v_a_4157_);
v___x_4159_ = lean_nat_dec_lt(v___x_4121_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4162_; 
lean_dec(v_a_4157_);
v___x_4160_ = lean_box(0);
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 1);
lean_ctor_set(v___x_4116_, 0, v___x_4160_);
v___x_4162_ = v___x_4116_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
else
{
lean_object* v___x_4164_; uint8_t v___x_4165_; 
lean_del_object(v___x_4116_);
v___x_4164_ = lean_box(0);
v___x_4165_ = lean_nat_dec_le(v___x_4158_, v___x_4158_);
if (v___x_4165_ == 0)
{
if (v___x_4159_ == 0)
{
lean_dec(v_a_4157_);
goto v___jp_4106_;
}
else
{
size_t v___x_4166_; size_t v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = ((size_t)0ULL);
v___x_4167_ = lean_usize_of_nat(v___x_4158_);
v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4157_, v___x_4166_, v___x_4167_, v___x_4164_, v___y_4104_);
lean_dec(v_a_4157_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_dec_ref(v___x_4168_);
goto v___jp_4106_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4168_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
else
{
size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = ((size_t)0ULL);
v___x_4178_ = lean_usize_of_nat(v___x_4158_);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4157_, v___x_4177_, v___x_4178_, v___x_4164_, v___y_4104_);
lean_dec(v_a_4157_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref(v___x_4179_);
goto v___jp_4106_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
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
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v_b_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_leanOpts_4100_);
v_a_4189_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4113_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4113_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
v___jp_4106_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_box(0);
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_4197_, lean_object* v_fst_4198_, lean_object* v___x_4199_, lean_object* v_leanOpts_4200_, lean_object* v_a_4201_, lean_object* v_b_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4197_, v_fst_4198_, v___x_4199_, v_leanOpts_4200_, v_a_4201_, v_b_4202_, v___y_4203_, v___y_4204_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v___x_4199_);
lean_dec_ref(v_fst_4198_);
lean_dec(v_upperBound_4197_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4209_, lean_object* v_toUpdate_4210_, lean_object* v_leanOpts_4211_, uint8_t v_updateToolchain_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_box(1);
v___x_4216_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4213_, v_ws_4209_, v_toUpdate_4210_, v___x_4215_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4216_);
if (v_updateToolchain_4212_ == 0)
{
lean_object* v_snd_4218_; uint8_t v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_snd_4218_ = lean_ctor_get(v_a_4217_, 1);
lean_inc(v_snd_4218_);
lean_dec(v_a_4217_);
v___x_4219_ = 1;
v___x_4220_ = lean_unsigned_to_nat(0u);
v___x_4221_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4211_, v___x_4219_, v_ws_4209_, v___x_4220_, v_snd_4218_, v_a_4213_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4238_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4238_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4238_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_fst_4226_; lean_object* v_snd_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4237_; 
v_fst_4226_ = lean_ctor_get(v_a_4222_, 0);
v_snd_4227_ = lean_ctor_get(v_a_4222_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_a_4222_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4229_ = v_a_4222_;
v_isShared_4230_ = v_isSharedCheck_4237_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_snd_4227_);
lean_inc(v_fst_4226_);
lean_dec(v_a_4222_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4237_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_fst_4226_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_snd_4227_);
v___x_4232_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4234_; 
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4232_);
v___x_4234_ = v___x_4224_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
v_a_4239_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4221_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4221_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_object* v_snd_4247_; lean_object* v_packages_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v_depConfigs_4251_; lean_object* v___x_4252_; lean_object* v___f_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_snd_4247_ = lean_ctor_get(v_a_4217_, 1);
lean_inc(v_snd_4247_);
lean_dec(v_a_4217_);
v_packages_4248_ = lean_ctor_get(v_ws_4209_, 4);
lean_inc_ref(v_packages_4248_);
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = lean_array_fget_borrowed(v_packages_4248_, v___x_4249_);
v_depConfigs_4251_ = lean_ctor_get(v___x_4250_, 12);
v___x_4252_ = lean_box(v_updateToolchain_4212_);
lean_inc_ref(v_ws_4209_);
lean_inc(v___x_4250_);
v___f_4253_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4253_, 0, v___x_4250_);
lean_closure_set(v___f_4253_, 1, v___x_4252_);
lean_closure_set(v___f_4253_, 2, v_ws_4209_);
v___x_4254_ = lean_array_get_size(v_depConfigs_4251_);
lean_inc_ref(v_depConfigs_4251_);
v___x_4255_ = l_Array_reverse___redArg(v_depConfigs_4251_);
v___x_4256_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4257_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4254_, v___f_4253_, v___x_4255_, v___x_4249_, v___x_4256_, v_snd_4247_, v_a_4213_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v_fst_4259_; lean_object* v_snd_4260_; lean_object* v___x_4261_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v_fst_4259_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_fst_4259_);
v_snd_4260_ = lean_ctor_get(v_a_4258_, 1);
lean_inc(v_snd_4260_);
lean_dec(v_a_4258_);
lean_inc_ref(v_ws_4209_);
v___x_4261_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4213_, v_ws_4209_, v_fst_4259_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v___x_4262_; 
lean_dec_ref(v___x_4261_);
lean_inc_ref(v_leanOpts_4211_);
v___x_4262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4254_, v_fst_4259_, v___x_4255_, v_leanOpts_4211_, v___x_4249_, v_ws_4209_, v_snd_4260_, v_a_4213_);
lean_dec_ref(v___x_4255_);
lean_dec(v_fst_4259_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v_fst_4264_; lean_object* v_snd_4265_; lean_object* v_packages_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref(v___x_4262_);
v_fst_4264_ = lean_ctor_get(v_a_4263_, 0);
lean_inc(v_fst_4264_);
v_snd_4265_ = lean_ctor_get(v_a_4263_, 1);
lean_inc(v_snd_4265_);
lean_dec(v_a_4263_);
v_packages_4266_ = lean_ctor_get(v_fst_4264_, 4);
v___x_4267_ = lean_array_get_size(v_packages_4248_);
lean_dec_ref(v_packages_4248_);
v___x_4268_ = lean_array_get_size(v_packages_4266_);
v___x_4269_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4268_, v_leanOpts_4211_, v___x_4267_, v_fst_4264_, v_snd_4265_, v_a_4213_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4291_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4291_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4291_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v_fst_4274_; lean_object* v_snd_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4290_; 
v_fst_4274_ = lean_ctor_get(v_a_4270_, 0);
v_snd_4275_ = lean_ctor_get(v_a_4270_, 1);
v_isSharedCheck_4290_ = !lean_is_exclusive(v_a_4270_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4277_ = v_a_4270_;
v_isShared_4278_ = v_isSharedCheck_4290_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_snd_4275_);
lean_inc(v_fst_4274_);
lean_dec(v_a_4270_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4290_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v_packages_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4285_; 
v_packages_4279_ = lean_ctor_get(v_fst_4274_, 4);
v___x_4280_ = lean_array_fget(v_packages_4279_, v___x_4249_);
lean_inc_ref(v_packages_4279_);
v___x_4281_ = l_Array_toSubarray___redArg(v_packages_4279_, v___x_4267_, v___x_4268_);
v___x_4282_ = l_Subarray_copy___redArg(v___x_4281_);
v___x_4283_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_4274_, v___x_4280_, v___x_4282_);
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 0, v___x_4283_);
v___x_4285_ = v___x_4277_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4283_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v_snd_4275_);
v___x_4285_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
lean_object* v___x_4287_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4285_);
v___x_4287_ = v___x_4272_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4285_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4269_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4269_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v_packages_4248_);
lean_dec_ref(v_leanOpts_4211_);
v_a_4300_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4262_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4262_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v_snd_4260_);
lean_dec(v_fst_4259_);
lean_dec_ref(v___x_4255_);
lean_dec_ref(v_packages_4248_);
lean_dec_ref(v_leanOpts_4211_);
lean_dec_ref(v_ws_4209_);
v_a_4308_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4261_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4261_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v___x_4255_);
lean_dec_ref(v_packages_4248_);
lean_dec_ref(v_leanOpts_4211_);
lean_dec_ref(v_ws_4209_);
v_a_4316_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4257_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4257_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec_ref(v_leanOpts_4211_);
lean_dec_ref(v_ws_4209_);
v_a_4324_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4216_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4216_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4332_, lean_object* v_toUpdate_4333_, lean_object* v_leanOpts_4334_, lean_object* v_updateToolchain_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
uint8_t v_updateToolchain_boxed_4338_; lean_object* v_res_4339_; 
v_updateToolchain_boxed_4338_ = lean_unbox(v_updateToolchain_4335_);
v_res_4339_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4332_, v_toUpdate_4333_, v_leanOpts_4334_, v_updateToolchain_boxed_4338_, v_a_4336_);
lean_dec_ref(v_a_4336_);
lean_dec(v_toUpdate_4333_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4340_, uint8_t v_reconfigure_4341_, lean_object* v_ws_4342_, lean_object* v_wsIdx_4343_, lean_object* v_h_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v___x_4348_; 
v___x_4348_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4340_, v_reconfigure_4341_, v_ws_4342_, v_wsIdx_4343_, v___y_4345_, v___y_4346_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4349_, lean_object* v_reconfigure_4350_, lean_object* v_ws_4351_, lean_object* v_wsIdx_4352_, lean_object* v_h_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
uint8_t v_reconfigure_boxed_4357_; lean_object* v_res_4358_; 
v_reconfigure_boxed_4357_ = lean_unbox(v_reconfigure_4350_);
v_res_4358_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4349_, v_reconfigure_boxed_4357_, v_ws_4351_, v_wsIdx_4352_, v_h_4353_, v___y_4354_, v___y_4355_);
lean_dec_ref(v___y_4355_);
lean_dec(v_wsIdx_4352_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4359_, lean_object* v_00_u03b2_4360_, lean_object* v_n_4361_, lean_object* v_f_4362_, lean_object* v_xs_4363_, lean_object* v_k_4364_, lean_object* v_h_4365_, lean_object* v_acc_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4361_, v_f_4362_, v_xs_4363_, v_k_4364_, v_acc_4366_, v___y_4367_, v___y_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4371_, lean_object* v_00_u03b2_4372_, lean_object* v_n_4373_, lean_object* v_f_4374_, lean_object* v_xs_4375_, lean_object* v_k_4376_, lean_object* v_h_4377_, lean_object* v_acc_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4371_, v_00_u03b2_4372_, v_n_4373_, v_f_4374_, v_xs_4375_, v_k_4376_, v_h_4377_, v_acc_4378_, v___y_4379_, v___y_4380_);
lean_dec_ref(v___y_4380_);
lean_dec_ref(v_xs_4375_);
lean_dec(v_n_4373_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_upperBound_4383_, lean_object* v_leanOpts_4384_, lean_object* v_inst_4385_, lean_object* v_R_4386_, lean_object* v_a_4387_, lean_object* v_b_4388_, lean_object* v_c_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_upperBound_4383_, v_leanOpts_4384_, v_a_4387_, v_b_4388_, v___y_4390_, v___y_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object* v_upperBound_4394_, lean_object* v_leanOpts_4395_, lean_object* v_inst_4396_, lean_object* v_R_4397_, lean_object* v_a_4398_, lean_object* v_b_4399_, lean_object* v_c_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_upperBound_4394_, v_leanOpts_4395_, v_inst_4396_, v_R_4397_, v_a_4398_, v_b_4399_, v_c_4400_, v___y_4401_, v___y_4402_);
lean_dec_ref(v___y_4402_);
lean_dec(v_upperBound_4394_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4405_, lean_object* v_fst_4406_, lean_object* v___x_4407_, lean_object* v_leanOpts_4408_, lean_object* v_inst_4409_, lean_object* v_R_4410_, lean_object* v_a_4411_, lean_object* v_b_4412_, lean_object* v_c_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4405_, v_fst_4406_, v___x_4407_, v_leanOpts_4408_, v_a_4411_, v_b_4412_, v___y_4414_, v___y_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4418_, lean_object* v_fst_4419_, lean_object* v___x_4420_, lean_object* v_leanOpts_4421_, lean_object* v_inst_4422_, lean_object* v_R_4423_, lean_object* v_a_4424_, lean_object* v_b_4425_, lean_object* v_c_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4418_, v_fst_4419_, v___x_4420_, v_leanOpts_4421_, v_inst_4422_, v_R_4423_, v_a_4424_, v_b_4425_, v_c_4426_, v___y_4427_, v___y_4428_);
lean_dec_ref(v___y_4428_);
lean_dec_ref(v___x_4420_);
lean_dec_ref(v_fst_4419_);
lean_dec(v_upperBound_4418_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object* v_upperBound_4431_, lean_object* v_leanOpts_4432_, uint8_t v_reconfigure_4433_, lean_object* v_inst_4434_, lean_object* v_R_4435_, lean_object* v_a_4436_, lean_object* v_b_4437_, lean_object* v_c_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v___x_4442_; 
v___x_4442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_upperBound_4431_, v_leanOpts_4432_, v_reconfigure_4433_, v_a_4436_, v_b_4437_, v___y_4439_, v___y_4440_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___boxed(lean_object* v_upperBound_4443_, lean_object* v_leanOpts_4444_, lean_object* v_reconfigure_4445_, lean_object* v_inst_4446_, lean_object* v_R_4447_, lean_object* v_a_4448_, lean_object* v_b_4449_, lean_object* v_c_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
uint8_t v_reconfigure_boxed_4454_; lean_object* v_res_4455_; 
v_reconfigure_boxed_4454_ = lean_unbox(v_reconfigure_4445_);
v_res_4455_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v_upperBound_4443_, v_leanOpts_4444_, v_reconfigure_boxed_4454_, v_inst_4446_, v_R_4447_, v_a_4448_, v_b_4449_, v_c_4450_, v___y_4451_, v___y_4452_);
lean_dec_ref(v___y_4452_);
lean_dec(v_upperBound_4443_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(lean_object* v_start_4456_, lean_object* v_pkg_4457_, lean_object* v_leanOpts_4458_, uint8_t v_reconfigure_4459_, lean_object* v_as_4460_, size_t v_i_4461_, size_t v_stop_4462_, lean_object* v_b_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v___x_4467_; 
v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4457_, v_leanOpts_4458_, v_reconfigure_4459_, v_as_4460_, v_i_4461_, v_stop_4462_, v_b_4463_, v___y_4464_, v___y_4465_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___boxed(lean_object* v_start_4468_, lean_object* v_pkg_4469_, lean_object* v_leanOpts_4470_, lean_object* v_reconfigure_4471_, lean_object* v_as_4472_, lean_object* v_i_4473_, lean_object* v_stop_4474_, lean_object* v_b_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
uint8_t v_reconfigure_boxed_4479_; size_t v_i_boxed_4480_; size_t v_stop_boxed_4481_; lean_object* v_res_4482_; 
v_reconfigure_boxed_4479_ = lean_unbox(v_reconfigure_4471_);
v_i_boxed_4480_ = lean_unbox_usize(v_i_4473_);
lean_dec(v_i_4473_);
v_stop_boxed_4481_ = lean_unbox_usize(v_stop_4474_);
lean_dec(v_stop_4474_);
v_res_4482_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(v_start_4468_, v_pkg_4469_, v_leanOpts_4470_, v_reconfigure_boxed_4479_, v_as_4472_, v_i_boxed_4480_, v_stop_boxed_4481_, v_b_4475_, v___y_4476_, v___y_4477_);
lean_dec_ref(v___y_4477_);
lean_dec_ref(v_as_4472_);
lean_dec(v_start_4468_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4483_, lean_object* v_msg_4484_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v_msg_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(lean_object* v_00_u03b2_4486_, lean_object* v_k_4487_, lean_object* v_v_4488_, lean_object* v_t_4489_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v_k_4487_, v_v_4488_, v_t_4489_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9(lean_object* v_init_4491_, lean_object* v_t_4492_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(v_init_4491_, v_t_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4494_, lean_object* v_as_4495_, size_t v_i_4496_, size_t v_stop_4497_, lean_object* v_b_4498_){
_start:
{
lean_object* v___y_4500_; uint8_t v___x_4504_; 
v___x_4504_ = lean_usize_dec_eq(v_i_4496_, v_stop_4497_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; lean_object* v_baseName_4506_; lean_object* v_relConfigFile_4507_; lean_object* v_relManifestFile_4508_; lean_object* v___x_4509_; 
v___x_4505_ = lean_array_uget_borrowed(v_as_4495_, v_i_4496_);
v_baseName_4506_ = lean_ctor_get(v___x_4505_, 1);
v_relConfigFile_4507_ = lean_ctor_get(v___x_4505_, 8);
v_relManifestFile_4508_ = lean_ctor_get(v___x_4505_, 9);
v___x_4509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4494_, v_baseName_4506_);
if (lean_obj_tag(v___x_4509_) == 0)
{
v___y_4500_ = v_b_4498_;
goto v___jp_4499_;
}
else
{
lean_object* v_val_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4531_; 
v_val_4510_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4512_ = v___x_4509_;
v_isShared_4513_ = v_isSharedCheck_4531_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_val_4510_);
lean_dec(v___x_4509_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4531_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v_name_4514_; lean_object* v_scope_4515_; uint8_t v_inherited_4516_; lean_object* v_src_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4528_; 
v_name_4514_ = lean_ctor_get(v_val_4510_, 0);
v_scope_4515_ = lean_ctor_get(v_val_4510_, 1);
v_inherited_4516_ = lean_ctor_get_uint8(v_val_4510_, sizeof(void*)*5);
v_src_4517_ = lean_ctor_get(v_val_4510_, 4);
v_isSharedCheck_4528_ = !lean_is_exclusive(v_val_4510_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; lean_object* v_unused_4530_; 
v_unused_4529_ = lean_ctor_get(v_val_4510_, 3);
lean_dec(v_unused_4529_);
v_unused_4530_ = lean_ctor_get(v_val_4510_, 2);
lean_dec(v_unused_4530_);
v___x_4519_ = v_val_4510_;
v_isShared_4520_ = v_isSharedCheck_4528_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_src_4517_);
lean_inc(v_scope_4515_);
lean_inc(v_name_4514_);
lean_dec(v_val_4510_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4528_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
lean_inc_ref(v_relManifestFile_4508_);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v_relManifestFile_4508_);
v___x_4522_ = v___x_4512_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_relManifestFile_4508_);
v___x_4522_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4524_; 
lean_inc_ref(v_relConfigFile_4507_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 3, v___x_4522_);
lean_ctor_set(v___x_4519_, 2, v_relConfigFile_4507_);
v___x_4524_ = v___x_4519_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_name_4514_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_scope_4515_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v_relConfigFile_4507_);
lean_ctor_set(v_reuseFailAlloc_4526_, 3, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4526_, 4, v_src_4517_);
lean_ctor_set_uint8(v_reuseFailAlloc_4526_, sizeof(void*)*5, v_inherited_4516_);
v___x_4524_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4525_; 
v___x_4525_ = lean_array_push(v_b_4498_, v___x_4524_);
v___y_4500_ = v___x_4525_;
goto v___jp_4499_;
}
}
}
}
}
}
else
{
return v_b_4498_;
}
v___jp_4499_:
{
size_t v___x_4501_; size_t v___x_4502_; 
v___x_4501_ = ((size_t)1ULL);
v___x_4502_ = lean_usize_add(v_i_4496_, v___x_4501_);
v_i_4496_ = v___x_4502_;
v_b_4498_ = v___y_4500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4532_, lean_object* v_as_4533_, lean_object* v_i_4534_, lean_object* v_stop_4535_, lean_object* v_b_4536_){
_start:
{
size_t v_i_boxed_4537_; size_t v_stop_boxed_4538_; lean_object* v_res_4539_; 
v_i_boxed_4537_ = lean_unbox_usize(v_i_4534_);
lean_dec(v_i_4534_);
v_stop_boxed_4538_ = lean_unbox_usize(v_stop_4535_);
lean_dec(v_stop_4535_);
v_res_4539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4532_, v_as_4533_, v_i_boxed_4537_, v_stop_boxed_4538_, v_b_4536_);
lean_dec_ref(v_as_4533_);
lean_dec(v_entries_4532_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4540_, lean_object* v_entries_4541_){
_start:
{
lean_object* v_packages_4543_; lean_object* v___y_4545_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_packages_4543_ = lean_ctor_get(v_ws_4540_, 4);
v___x_4560_ = lean_unsigned_to_nat(0u);
v___x_4561_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4562_ = lean_array_get_size(v_packages_4543_);
v___x_4563_ = lean_nat_dec_lt(v___x_4560_, v___x_4562_);
if (v___x_4563_ == 0)
{
v___y_4545_ = v___x_4561_;
goto v___jp_4544_;
}
else
{
uint8_t v___x_4564_; 
v___x_4564_ = lean_nat_dec_le(v___x_4562_, v___x_4562_);
if (v___x_4564_ == 0)
{
if (v___x_4563_ == 0)
{
v___y_4545_ = v___x_4561_;
goto v___jp_4544_;
}
else
{
size_t v___x_4565_; size_t v___x_4566_; lean_object* v___x_4567_; 
v___x_4565_ = ((size_t)0ULL);
v___x_4566_ = lean_usize_of_nat(v___x_4562_);
v___x_4567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4541_, v_packages_4543_, v___x_4565_, v___x_4566_, v___x_4561_);
v___y_4545_ = v___x_4567_;
goto v___jp_4544_;
}
}
else
{
size_t v___x_4568_; size_t v___x_4569_; lean_object* v___x_4570_; 
v___x_4568_ = ((size_t)0ULL);
v___x_4569_ = lean_usize_of_nat(v___x_4562_);
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4541_, v_packages_4543_, v___x_4568_, v___x_4569_, v___x_4561_);
v___y_4545_ = v___x_4570_;
goto v___jp_4544_;
}
}
v___jp_4544_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v_config_4548_; lean_object* v_baseName_4549_; lean_object* v_dir_4550_; lean_object* v_relManifestFile_4551_; lean_object* v_toWorkspaceConfig_4552_; uint8_t v_fixedToolchain_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v_manifest_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = lean_array_fget_borrowed(v_packages_4543_, v___x_4546_);
v_config_4548_ = lean_ctor_get(v___x_4547_, 6);
v_baseName_4549_ = lean_ctor_get(v___x_4547_, 1);
v_dir_4550_ = lean_ctor_get(v___x_4547_, 4);
v_relManifestFile_4551_ = lean_ctor_get(v___x_4547_, 9);
v_toWorkspaceConfig_4552_ = lean_ctor_get(v_config_4548_, 0);
v_fixedToolchain_4553_ = lean_ctor_get_uint8(v_config_4548_, sizeof(void*)*26 + 6);
v___x_4554_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4552_);
v___x_4555_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4552_);
v___x_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_inc(v_baseName_4549_);
v_manifest_4557_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4557_, 0, v_baseName_4549_);
lean_ctor_set(v_manifest_4557_, 1, v___x_4554_);
lean_ctor_set(v_manifest_4557_, 2, v___x_4556_);
lean_ctor_set(v_manifest_4557_, 3, v___y_4545_);
lean_ctor_set_uint8(v_manifest_4557_, sizeof(void*)*4, v_fixedToolchain_4553_);
lean_inc_ref(v_relManifestFile_4551_);
lean_inc_ref(v_dir_4550_);
v___x_4558_ = l_Lake_joinRelative(v_dir_4550_, v_relManifestFile_4551_);
v___x_4559_ = l_Lake_Manifest_save(v_manifest_4557_, v___x_4558_);
lean_dec_ref(v___x_4558_);
return v___x_4559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4571_, lean_object* v_entries_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4571_, v_entries_4572_);
lean_dec(v_entries_4572_);
lean_dec_ref(v_ws_4571_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4575_, lean_object* v_as_4576_, size_t v_i_4577_, size_t v_stop_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_a_4584_; lean_object* v___y_4589_; uint8_t v___x_4594_; 
v___x_4594_ = lean_usize_dec_eq(v_i_4577_, v_stop_4578_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_9317__overap_4597_; lean_object* v___x_4598_; 
v___x_4595_ = lean_unsigned_to_nat(0u);
v___x_4596_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9317__overap_4597_ = lean_array_uget_borrowed(v_as_4576_, v_i_4577_);
lean_inc(v___x_9317__overap_4597_);
lean_inc(v___y_4580_);
lean_inc_ref(v_pkg_4575_);
v___x_4598_ = lean_apply_4(v___x_9317__overap_4597_, v_pkg_4575_, v___y_4580_, v___x_4596_, lean_box(0));
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v_a_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
v_a_4600_ = lean_ctor_get(v___x_4598_, 1);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4598_);
v___x_4601_ = lean_array_get_size(v_a_4600_);
v___x_4602_ = lean_nat_dec_lt(v___x_4595_, v___x_4601_);
if (v___x_4602_ == 0)
{
lean_dec(v_a_4600_);
v_a_4584_ = v_a_4599_;
goto v___jp_4583_;
}
else
{
lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4603_ = lean_box(0);
v___x_4604_ = lean_nat_dec_le(v___x_4601_, v___x_4601_);
if (v___x_4604_ == 0)
{
if (v___x_4602_ == 0)
{
lean_dec(v_a_4600_);
v_a_4584_ = v_a_4599_;
goto v___jp_4583_;
}
else
{
size_t v___x_4605_; size_t v___x_4606_; lean_object* v___x_4607_; 
v___x_4605_ = ((size_t)0ULL);
v___x_4606_ = lean_usize_of_nat(v___x_4601_);
v___x_4607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4600_, v___x_4605_, v___x_4606_, v___x_4603_, v___y_4581_);
lean_dec(v_a_4600_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_dec_ref(v___x_4607_);
v_a_4584_ = v_a_4599_;
goto v___jp_4583_;
}
else
{
lean_dec(v_a_4599_);
v___y_4589_ = v___x_4607_;
goto v___jp_4588_;
}
}
}
else
{
size_t v___x_4608_; size_t v___x_4609_; lean_object* v___x_4610_; 
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = lean_usize_of_nat(v___x_4601_);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4600_, v___x_4608_, v___x_4609_, v___x_4603_, v___y_4581_);
lean_dec(v_a_4600_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_dec_ref(v___x_4610_);
v_a_4584_ = v_a_4599_;
goto v___jp_4583_;
}
else
{
lean_dec(v_a_4599_);
v___y_4589_ = v___x_4610_;
goto v___jp_4588_;
}
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4612_; uint8_t v___x_4613_; 
v_a_4611_ = lean_ctor_get(v___x_4598_, 1);
lean_inc(v_a_4611_);
lean_dec_ref(v___x_4598_);
v___x_4612_ = lean_array_get_size(v_a_4611_);
v___x_4613_ = lean_nat_dec_lt(v___x_4595_, v___x_4612_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
lean_dec(v_a_4611_);
lean_dec_ref(v_pkg_4575_);
v___x_4614_ = lean_box(0);
v___x_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
else
{
lean_object* v___x_4616_; uint8_t v___x_4617_; 
v___x_4616_ = lean_box(0);
v___x_4617_ = lean_nat_dec_le(v___x_4612_, v___x_4612_);
if (v___x_4617_ == 0)
{
if (v___x_4613_ == 0)
{
lean_dec(v_a_4611_);
lean_dec_ref(v_pkg_4575_);
goto v___jp_4591_;
}
else
{
size_t v___x_4618_; size_t v___x_4619_; lean_object* v___x_4620_; 
v___x_4618_ = ((size_t)0ULL);
v___x_4619_ = lean_usize_of_nat(v___x_4612_);
v___x_4620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4611_, v___x_4618_, v___x_4619_, v___x_4616_, v___y_4581_);
lean_dec(v_a_4611_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_dec_ref(v___x_4620_);
lean_dec_ref(v_pkg_4575_);
goto v___jp_4591_;
}
else
{
v___y_4589_ = v___x_4620_;
goto v___jp_4588_;
}
}
}
else
{
size_t v___x_4621_; size_t v___x_4622_; lean_object* v___x_4623_; 
v___x_4621_ = ((size_t)0ULL);
v___x_4622_ = lean_usize_of_nat(v___x_4612_);
v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4611_, v___x_4621_, v___x_4622_, v___x_4616_, v___y_4581_);
lean_dec(v_a_4611_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_dec_ref(v___x_4623_);
lean_dec_ref(v_pkg_4575_);
goto v___jp_4591_;
}
else
{
v___y_4589_ = v___x_4623_;
goto v___jp_4588_;
}
}
}
}
}
else
{
lean_object* v___x_4624_; 
lean_dec_ref(v_pkg_4575_);
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v_b_4579_);
return v___x_4624_;
}
v___jp_4583_:
{
size_t v___x_4585_; size_t v___x_4586_; 
v___x_4585_ = ((size_t)1ULL);
v___x_4586_ = lean_usize_add(v_i_4577_, v___x_4585_);
v_i_4577_ = v___x_4586_;
v_b_4579_ = v_a_4584_;
goto _start;
}
v___jp_4588_:
{
if (lean_obj_tag(v___y_4589_) == 0)
{
lean_object* v_a_4590_; 
v_a_4590_ = lean_ctor_get(v___y_4589_, 0);
lean_inc(v_a_4590_);
lean_dec_ref(v___y_4589_);
v_a_4584_ = v_a_4590_;
goto v___jp_4583_;
}
else
{
lean_dec_ref(v_pkg_4575_);
return v___y_4589_;
}
}
v___jp_4591_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = lean_box(0);
v___x_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4625_, lean_object* v_as_4626_, lean_object* v_i_4627_, lean_object* v_stop_4628_, lean_object* v_b_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
size_t v_i_boxed_4633_; size_t v_stop_boxed_4634_; lean_object* v_res_4635_; 
v_i_boxed_4633_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_stop_boxed_4634_ = lean_unbox_usize(v_stop_4628_);
lean_dec(v_stop_4628_);
v_res_4635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4625_, v_as_4626_, v_i_boxed_4633_, v_stop_boxed_4634_, v_b_4629_, v___y_4630_, v___y_4631_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v_as_4626_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v_baseName_4641_; lean_object* v_postUpdateHooks_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_baseName_4641_ = lean_ctor_get(v_pkg_4637_, 1);
v_postUpdateHooks_4642_ = lean_ctor_get(v_pkg_4637_, 19);
lean_inc_ref(v_postUpdateHooks_4642_);
v___x_4643_ = lean_array_get_size(v_postUpdateHooks_4642_);
v___x_4644_ = lean_unsigned_to_nat(0u);
v___x_4645_ = lean_nat_dec_eq(v___x_4643_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
lean_inc(v_baseName_4641_);
v___x_4646_ = l_Lean_Name_toString(v_baseName_4641_, v___x_4645_);
v___x_4647_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4648_ = lean_string_append(v___x_4646_, v___x_4647_);
v___x_4649_ = 1;
v___x_4650_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4650_, 0, v___x_4648_);
lean_ctor_set_uint8(v___x_4650_, sizeof(void*)*1, v___x_4649_);
lean_inc_ref(v_a_4639_);
v___x_4651_ = lean_apply_2(v_a_4639_, v___x_4650_, lean_box(0));
v___x_4652_ = lean_box(0);
v___x_4653_ = lean_nat_dec_lt(v___x_4644_, v___x_4643_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; 
lean_dec_ref(v_postUpdateHooks_4642_);
lean_dec_ref(v_pkg_4637_);
v___x_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4652_);
return v___x_4654_;
}
else
{
uint8_t v___x_4655_; 
v___x_4655_ = lean_nat_dec_le(v___x_4643_, v___x_4643_);
if (v___x_4655_ == 0)
{
if (v___x_4653_ == 0)
{
lean_object* v___x_4656_; 
lean_dec_ref(v_postUpdateHooks_4642_);
lean_dec_ref(v_pkg_4637_);
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4652_);
return v___x_4656_;
}
else
{
size_t v___x_4657_; size_t v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = ((size_t)0ULL);
v___x_4658_ = lean_usize_of_nat(v___x_4643_);
v___x_4659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4637_, v_postUpdateHooks_4642_, v___x_4657_, v___x_4658_, v___x_4652_, v_a_4638_, v_a_4639_);
lean_dec_ref(v_postUpdateHooks_4642_);
return v___x_4659_;
}
}
else
{
size_t v___x_4660_; size_t v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = ((size_t)0ULL);
v___x_4661_ = lean_usize_of_nat(v___x_4643_);
v___x_4662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4637_, v_postUpdateHooks_4642_, v___x_4660_, v___x_4661_, v___x_4652_, v_a_4638_, v_a_4639_);
lean_dec_ref(v_postUpdateHooks_4642_);
return v___x_4662_;
}
}
}
else
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
lean_dec_ref(v_postUpdateHooks_4642_);
lean_dec_ref(v_pkg_4637_);
v___x_4663_ = lean_box(0);
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
return v___x_4664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4665_, v_a_4666_, v_a_4667_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4670_, lean_object* v_ws_4671_, lean_object* v_toUpdate_4672_, lean_object* v_leanOpts_4673_, uint8_t v_updateToolchain_4674_){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_box(1);
v___x_4677_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4670_, v_ws_4671_, v_toUpdate_4672_, v___x_4676_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
if (v_updateToolchain_4674_ == 0)
{
lean_object* v_snd_4679_; uint8_t v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v_snd_4679_ = lean_ctor_get(v_a_4678_, 1);
lean_inc(v_snd_4679_);
lean_dec(v_a_4678_);
v___x_4680_ = 1;
v___x_4681_ = lean_unsigned_to_nat(0u);
v___x_4682_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4673_, v___x_4680_, v_ws_4671_, v___x_4681_, v_snd_4679_, v_a_4670_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4699_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4699_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4699_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v_fst_4687_; lean_object* v_snd_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4698_; 
v_fst_4687_ = lean_ctor_get(v_a_4683_, 0);
v_snd_4688_ = lean_ctor_get(v_a_4683_, 1);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_a_4683_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4690_ = v_a_4683_;
v_isShared_4691_ = v_isSharedCheck_4698_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_snd_4688_);
lean_inc(v_fst_4687_);
lean_dec(v_a_4683_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4698_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_fst_4687_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_snd_4688_);
v___x_4693_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
lean_object* v___x_4695_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4693_);
v___x_4695_ = v___x_4685_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
v_a_4700_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4682_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4682_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
else
{
lean_object* v_snd_4708_; lean_object* v_packages_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v_depConfigs_4712_; lean_object* v___x_4713_; lean_object* v___f_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v_snd_4708_ = lean_ctor_get(v_a_4678_, 1);
lean_inc(v_snd_4708_);
lean_dec(v_a_4678_);
v_packages_4709_ = lean_ctor_get(v_ws_4671_, 4);
lean_inc_ref(v_packages_4709_);
v___x_4710_ = lean_unsigned_to_nat(0u);
v___x_4711_ = lean_array_fget_borrowed(v_packages_4709_, v___x_4710_);
v_depConfigs_4712_ = lean_ctor_get(v___x_4711_, 12);
v___x_4713_ = lean_box(v_updateToolchain_4674_);
lean_inc_ref(v_ws_4671_);
lean_inc(v___x_4711_);
v___f_4714_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4714_, 0, v___x_4711_);
lean_closure_set(v___f_4714_, 1, v___x_4713_);
lean_closure_set(v___f_4714_, 2, v_ws_4671_);
v___x_4715_ = lean_array_get_size(v_depConfigs_4712_);
lean_inc_ref(v_depConfigs_4712_);
v___x_4716_ = l_Array_reverse___redArg(v_depConfigs_4712_);
v___x_4717_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4718_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4715_, v___f_4714_, v___x_4716_, v___x_4710_, v___x_4717_, v_snd_4708_, v_a_4670_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v_fst_4720_; lean_object* v_snd_4721_; lean_object* v___x_4722_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref(v___x_4718_);
v_fst_4720_ = lean_ctor_get(v_a_4719_, 0);
lean_inc(v_fst_4720_);
v_snd_4721_ = lean_ctor_get(v_a_4719_, 1);
lean_inc(v_snd_4721_);
lean_dec(v_a_4719_);
lean_inc_ref(v_ws_4671_);
v___x_4722_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4670_, v_ws_4671_, v_fst_4720_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v___x_4723_; 
lean_dec_ref(v___x_4722_);
lean_inc_ref(v_leanOpts_4673_);
v___x_4723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4715_, v_fst_4720_, v___x_4716_, v_leanOpts_4673_, v___x_4710_, v_ws_4671_, v_snd_4721_, v_a_4670_);
lean_dec_ref(v___x_4716_);
lean_dec(v_fst_4720_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v_fst_4725_; lean_object* v_snd_4726_; lean_object* v_packages_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref(v___x_4723_);
v_fst_4725_ = lean_ctor_get(v_a_4724_, 0);
lean_inc(v_fst_4725_);
v_snd_4726_ = lean_ctor_get(v_a_4724_, 1);
lean_inc(v_snd_4726_);
lean_dec(v_a_4724_);
v_packages_4727_ = lean_ctor_get(v_fst_4725_, 4);
v___x_4728_ = lean_array_get_size(v_packages_4709_);
lean_dec_ref(v_packages_4709_);
v___x_4729_ = lean_array_get_size(v_packages_4727_);
v___x_4730_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4729_, v_leanOpts_4673_, v___x_4728_, v_fst_4725_, v_snd_4726_, v_a_4670_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4752_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4733_ = v___x_4730_;
v_isShared_4734_ = v_isSharedCheck_4752_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4730_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4752_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v_fst_4735_; lean_object* v_snd_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4751_; 
v_fst_4735_ = lean_ctor_get(v_a_4731_, 0);
v_snd_4736_ = lean_ctor_get(v_a_4731_, 1);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_a_4731_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4738_ = v_a_4731_;
v_isShared_4739_ = v_isSharedCheck_4751_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_snd_4736_);
lean_inc(v_fst_4735_);
lean_dec(v_a_4731_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4751_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v_packages_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
v_packages_4740_ = lean_ctor_get(v_fst_4735_, 4);
v___x_4741_ = lean_array_fget(v_packages_4740_, v___x_4710_);
lean_inc_ref(v_packages_4740_);
v___x_4742_ = l_Array_toSubarray___redArg(v_packages_4740_, v___x_4728_, v___x_4729_);
v___x_4743_ = l_Subarray_copy___redArg(v___x_4742_);
v___x_4744_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_4735_, v___x_4741_, v___x_4743_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4744_);
v___x_4746_ = v___x_4738_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_snd_4736_);
v___x_4746_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4748_; 
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 0, v___x_4746_);
v___x_4748_ = v___x_4733_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
v_a_4753_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4730_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4730_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v_packages_4709_);
lean_dec_ref(v_leanOpts_4673_);
v_a_4761_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4723_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4723_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
lean_dec(v_snd_4721_);
lean_dec(v_fst_4720_);
lean_dec_ref(v___x_4716_);
lean_dec_ref(v_packages_4709_);
lean_dec_ref(v_leanOpts_4673_);
lean_dec_ref(v_ws_4671_);
v_a_4769_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4722_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4722_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
lean_dec_ref(v___x_4716_);
lean_dec_ref(v_packages_4709_);
lean_dec_ref(v_leanOpts_4673_);
lean_dec_ref(v_ws_4671_);
v_a_4777_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4718_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4718_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4792_; 
lean_dec_ref(v_leanOpts_4673_);
lean_dec_ref(v_ws_4671_);
v_a_4785_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4787_ = v___x_4677_;
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4677_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4793_, lean_object* v_ws_4794_, lean_object* v_toUpdate_4795_, lean_object* v_leanOpts_4796_, lean_object* v_updateToolchain_4797_, lean_object* v_a_4798_){
_start:
{
uint8_t v_updateToolchain_boxed_4799_; lean_object* v_res_4800_; 
v_updateToolchain_boxed_4799_ = lean_unbox(v_updateToolchain_4797_);
v_res_4800_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4793_, v_ws_4794_, v_toUpdate_4795_, v_leanOpts_4796_, v_updateToolchain_boxed_4799_);
lean_dec(v_toUpdate_4795_);
lean_dec_ref(v_a_4793_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4801_, size_t v_i_4802_, size_t v_stop_4803_, lean_object* v_b_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
uint8_t v___x_4808_; 
v___x_4808_ = lean_usize_dec_eq(v_i_4802_, v_stop_4803_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = lean_array_uget_borrowed(v_as_4801_, v_i_4802_);
lean_inc(v___x_4809_);
v___x_4810_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4809_, v___y_4805_, v___y_4806_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; size_t v___x_4812_; size_t v___x_4813_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_a_4811_);
lean_dec_ref(v___x_4810_);
v___x_4812_ = ((size_t)1ULL);
v___x_4813_ = lean_usize_add(v_i_4802_, v___x_4812_);
v_i_4802_ = v___x_4813_;
v_b_4804_ = v_a_4811_;
goto _start;
}
else
{
return v___x_4810_;
}
}
else
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v_b_4804_);
return v___x_4815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4816_, lean_object* v_i_4817_, lean_object* v_stop_4818_, lean_object* v_b_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
size_t v_i_boxed_4823_; size_t v_stop_boxed_4824_; lean_object* v_res_4825_; 
v_i_boxed_4823_ = lean_unbox_usize(v_i_4817_);
lean_dec(v_i_4817_);
v_stop_boxed_4824_ = lean_unbox_usize(v_stop_4818_);
lean_dec(v_stop_4818_);
v_res_4825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4816_, v_i_boxed_4823_, v_stop_boxed_4824_, v_b_4819_, v___y_4820_, v___y_4821_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v_as_4816_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4826_, lean_object* v_toUpdate_4827_, lean_object* v_leanOpts_4828_, uint8_t v_updateToolchain_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4830_, v_ws_4826_, v_toUpdate_4827_, v_leanOpts_4828_, v_updateToolchain_4829_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v_fst_4834_; lean_object* v_snd_4835_; lean_object* v___y_4837_; lean_object* v___x_4854_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_a_4833_);
lean_dec_ref(v___x_4832_);
v_fst_4834_ = lean_ctor_get(v_a_4833_, 0);
lean_inc(v_fst_4834_);
v_snd_4835_ = lean_ctor_get(v_a_4833_, 1);
lean_inc(v_snd_4835_);
lean_dec(v_a_4833_);
v___x_4854_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4834_, v_snd_4835_);
lean_dec(v_snd_4835_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4876_; 
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4876_ == 0)
{
lean_object* v_unused_4877_; 
v_unused_4877_ = lean_ctor_get(v___x_4854_, 0);
lean_dec(v_unused_4877_);
v___x_4856_ = v___x_4854_;
v_isShared_4857_ = v_isSharedCheck_4876_;
goto v_resetjp_4855_;
}
else
{
lean_dec(v___x_4854_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4876_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v_packages_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v_packages_4858_ = lean_ctor_get(v_fst_4834_, 4);
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = lean_array_get_size(v_packages_4858_);
v___x_4861_ = lean_nat_dec_lt(v___x_4859_, v___x_4860_);
if (v___x_4861_ == 0)
{
lean_object* v___x_4863_; 
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v_fst_4834_);
v___x_4863_ = v___x_4856_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_fst_4834_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
else
{
lean_object* v___x_4865_; uint8_t v___x_4866_; 
v___x_4865_ = lean_box(0);
v___x_4866_ = lean_nat_dec_le(v___x_4860_, v___x_4860_);
if (v___x_4866_ == 0)
{
if (v___x_4861_ == 0)
{
lean_object* v___x_4868_; 
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v_fst_4834_);
v___x_4868_ = v___x_4856_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_fst_4834_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
else
{
size_t v___x_4870_; size_t v___x_4871_; lean_object* v___x_4872_; 
lean_del_object(v___x_4856_);
v___x_4870_ = ((size_t)0ULL);
v___x_4871_ = lean_usize_of_nat(v___x_4860_);
v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4858_, v___x_4870_, v___x_4871_, v___x_4865_, v_fst_4834_, v_a_4830_);
v___y_4837_ = v___x_4872_;
goto v___jp_4836_;
}
}
else
{
size_t v___x_4873_; size_t v___x_4874_; lean_object* v___x_4875_; 
lean_del_object(v___x_4856_);
v___x_4873_ = ((size_t)0ULL);
v___x_4874_ = lean_usize_of_nat(v___x_4860_);
v___x_4875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4858_, v___x_4873_, v___x_4874_, v___x_4865_, v_fst_4834_, v_a_4830_);
v___y_4837_ = v___x_4875_;
goto v___jp_4836_;
}
}
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4890_; 
lean_dec(v_fst_4834_);
v_a_4878_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4880_ = v___x_4854_;
v_isShared_4881_ = v_isSharedCheck_4890_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4854_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4890_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; uint8_t v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4882_ = lean_io_error_to_string(v_a_4878_);
v___x_4883_ = 3;
v___x_4884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4884_, 0, v___x_4882_);
lean_ctor_set_uint8(v___x_4884_, sizeof(void*)*1, v___x_4883_);
lean_inc_ref(v_a_4830_);
v___x_4885_ = lean_apply_2(v_a_4830_, v___x_4884_, lean_box(0));
v___x_4886_ = lean_box(0);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4886_);
v___x_4888_ = v___x_4880_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
v___jp_4836_:
{
if (lean_obj_tag(v___y_4837_) == 0)
{
lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
v_isSharedCheck_4844_ = !lean_is_exclusive(v___y_4837_);
if (v_isSharedCheck_4844_ == 0)
{
lean_object* v_unused_4845_; 
v_unused_4845_ = lean_ctor_get(v___y_4837_, 0);
lean_dec(v_unused_4845_);
v___x_4839_ = v___y_4837_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_dec(v___y_4837_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 0, v_fst_4834_);
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_fst_4834_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec(v_fst_4834_);
v_a_4846_ = lean_ctor_get(v___y_4837_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___y_4837_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___y_4837_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___y_4837_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
v_a_4891_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4832_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4832_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4899_, lean_object* v_toUpdate_4900_, lean_object* v_leanOpts_4901_, lean_object* v_updateToolchain_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_){
_start:
{
uint8_t v_updateToolchain_boxed_4905_; lean_object* v_res_4906_; 
v_updateToolchain_boxed_4905_ = lean_unbox(v_updateToolchain_4902_);
v_res_4906_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4899_, v_toUpdate_4900_, v_leanOpts_4901_, v_updateToolchain_boxed_4905_, v_a_4903_);
lean_dec_ref(v_a_4903_);
lean_dec(v_toUpdate_4900_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4911_, lean_object* v_what_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_name_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_name_4915_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_name_4915_);
lean_dec_ref(v___x_4911_);
v___x_4916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4917_ = lean_string_append(v___x_4916_, v_what_4912_);
v___x_4918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4919_ = lean_string_append(v___x_4917_, v___x_4918_);
v___x_4920_ = 1;
v___x_4921_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4915_, v___x_4920_);
v___x_4922_ = lean_string_append(v___x_4919_, v___x_4921_);
v___x_4923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4924_ = lean_string_append(v___x_4922_, v___x_4923_);
v___x_4925_ = lean_string_append(v___x_4924_, v___x_4921_);
lean_dec_ref(v___x_4921_);
v___x_4926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4927_ = lean_string_append(v___x_4925_, v___x_4926_);
v___x_4928_ = 2;
v___x_4929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4929_, 0, v___x_4927_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1, v___x_4928_);
lean_inc_ref(v___y_4913_);
v___x_4930_ = lean_apply_2(v___y_4913_, v___x_4929_, lean_box(0));
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4932_, lean_object* v_what_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4932_, v_what_4933_, v___y_4934_);
lean_dec_ref(v___y_4934_);
lean_dec_ref(v_what_4933_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4940_, lean_object* v_as_4941_, size_t v_i_4942_, size_t v_stop_4943_, lean_object* v_b_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_a_4948_; lean_object* v___y_4953_; uint8_t v___x_4955_; 
v___x_4955_ = lean_usize_dec_eq(v_i_4942_, v_stop_4943_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; lean_object* v_src_x3f_4957_; 
v___x_4956_ = lean_array_uget_borrowed(v_as_4941_, v_i_4942_);
v_src_x3f_4957_ = lean_ctor_get(v___x_4956_, 3);
if (lean_obj_tag(v_src_x3f_4957_) == 1)
{
lean_object* v_name_4958_; lean_object* v_val_4959_; lean_object* v___x_4960_; 
v_name_4958_ = lean_ctor_get(v___x_4956_, 0);
v_val_4959_ = lean_ctor_get(v_src_x3f_4957_, 0);
v___x_4960_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4940_, v_name_4958_);
if (lean_obj_tag(v___x_4960_) == 1)
{
lean_object* v_val_4961_; lean_object* v___y_4963_; lean_object* v___y_4967_; 
v_val_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_val_4961_);
lean_dec_ref(v___x_4960_);
if (lean_obj_tag(v_val_4959_) == 0)
{
lean_object* v_src_4970_; 
v_src_4970_ = lean_ctor_get(v_val_4961_, 4);
lean_inc_ref(v_src_4970_);
lean_dec(v_val_4961_);
if (lean_obj_tag(v_src_4970_) == 0)
{
lean_object* v___x_4971_; 
lean_dec_ref(v_src_4970_);
v___x_4971_ = lean_box(0);
v_a_4948_ = v___x_4971_;
goto v___jp_4947_;
}
else
{
lean_dec_ref(v_src_4970_);
v___y_4967_ = v___y_4945_;
goto v___jp_4966_;
}
}
else
{
lean_object* v_src_4972_; 
v_src_4972_ = lean_ctor_get(v_val_4961_, 4);
lean_inc_ref(v_src_4972_);
lean_dec(v_val_4961_);
if (lean_obj_tag(v_src_4972_) == 1)
{
lean_object* v_url_4973_; lean_object* v_rev_4974_; lean_object* v_url_4975_; lean_object* v_inputRev_x3f_4976_; lean_object* v___y_4978_; uint8_t v___x_4985_; 
v_url_4973_ = lean_ctor_get(v_val_4959_, 0);
v_rev_4974_ = lean_ctor_get(v_val_4959_, 1);
v_url_4975_ = lean_ctor_get(v_src_4972_, 0);
lean_inc_ref(v_url_4975_);
v_inputRev_x3f_4976_ = lean_ctor_get(v_src_4972_, 2);
lean_inc(v_inputRev_x3f_4976_);
lean_dec_ref(v_src_4972_);
v___x_4985_ = lean_string_dec_eq(v_url_4973_, v_url_4975_);
lean_dec_ref(v_url_4975_);
if (v___x_4985_ == 0)
{
goto v___jp_4982_;
}
else
{
if (v___x_4955_ == 0)
{
v___y_4978_ = v___y_4945_;
goto v___jp_4977_;
}
else
{
goto v___jp_4982_;
}
}
v___jp_4977_:
{
lean_object* v___x_4979_; uint8_t v___x_4980_; 
v___x_4979_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4974_);
v___x_4980_ = l_Option_instDecidableEq___redArg(v___x_4979_, v_rev_4974_, v_inputRev_x3f_4976_);
if (v___x_4980_ == 0)
{
v___y_4963_ = v___y_4978_;
goto v___jp_4962_;
}
else
{
if (v___x_4955_ == 0)
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_box(0);
v_a_4948_ = v___x_4981_;
goto v___jp_4947_;
}
else
{
v___y_4963_ = v___y_4978_;
goto v___jp_4962_;
}
}
}
v___jp_4982_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4956_);
v___x_4984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4956_, v___x_4983_, v___y_4945_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_dec_ref(v___x_4984_);
v___y_4978_ = v___y_4945_;
goto v___jp_4977_;
}
else
{
lean_dec(v_inputRev_x3f_4976_);
return v___x_4984_;
}
}
}
else
{
lean_dec_ref(v_src_4972_);
v___y_4967_ = v___y_4945_;
goto v___jp_4966_;
}
}
v___jp_4962_:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4956_);
v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4956_, v___x_4964_, v___y_4963_);
v___y_4953_ = v___x_4965_;
goto v___jp_4952_;
}
v___jp_4966_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4956_);
v___x_4969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4956_, v___x_4968_, v___y_4967_);
v___y_4953_ = v___x_4969_;
goto v___jp_4952_;
}
}
else
{
lean_object* v___x_4986_; 
lean_dec(v___x_4960_);
v___x_4986_ = lean_box(0);
v_a_4948_ = v___x_4986_;
goto v___jp_4947_;
}
}
else
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_box(0);
v_a_4948_ = v___x_4987_;
goto v___jp_4947_;
}
}
else
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_b_4944_);
return v___x_4988_;
}
v___jp_4947_:
{
size_t v___x_4949_; size_t v___x_4950_; 
v___x_4949_ = ((size_t)1ULL);
v___x_4950_ = lean_usize_add(v_i_4942_, v___x_4949_);
v_i_4942_ = v___x_4950_;
v_b_4944_ = v_a_4948_;
goto _start;
}
v___jp_4952_:
{
if (lean_obj_tag(v___y_4953_) == 0)
{
lean_object* v_a_4954_; 
v_a_4954_ = lean_ctor_get(v___y_4953_, 0);
lean_inc(v_a_4954_);
lean_dec_ref(v___y_4953_);
v_a_4948_ = v_a_4954_;
goto v___jp_4947_;
}
else
{
return v___y_4953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4989_, lean_object* v_as_4990_, lean_object* v_i_4991_, lean_object* v_stop_4992_, lean_object* v_b_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
size_t v_i_boxed_4996_; size_t v_stop_boxed_4997_; lean_object* v_res_4998_; 
v_i_boxed_4996_ = lean_unbox_usize(v_i_4991_);
lean_dec(v_i_4991_);
v_stop_boxed_4997_ = lean_unbox_usize(v_stop_4992_);
lean_dec(v_stop_4992_);
v_res_4998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4989_, v_as_4990_, v_i_boxed_4996_, v_stop_boxed_4997_, v_b_4993_, v___y_4994_);
lean_dec_ref(v___y_4994_);
lean_dec_ref(v_as_4990_);
lean_dec(v_pkgEntries_4989_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4999_, lean_object* v_deps_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; 
v___x_5003_ = lean_unsigned_to_nat(0u);
v___x_5004_ = lean_array_get_size(v_deps_5000_);
v___x_5005_ = lean_box(0);
v___x_5006_ = lean_nat_dec_lt(v___x_5003_, v___x_5004_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5005_);
return v___x_5007_;
}
else
{
uint8_t v___x_5008_; 
v___x_5008_ = lean_nat_dec_le(v___x_5004_, v___x_5004_);
if (v___x_5008_ == 0)
{
if (v___x_5006_ == 0)
{
lean_object* v___x_5009_; 
v___x_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5005_);
return v___x_5009_;
}
else
{
size_t v___x_5010_; size_t v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = ((size_t)0ULL);
v___x_5011_ = lean_usize_of_nat(v___x_5004_);
v___x_5012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4999_, v_deps_5000_, v___x_5010_, v___x_5011_, v___x_5005_, v_a_5001_);
return v___x_5012_;
}
}
else
{
size_t v___x_5013_; size_t v___x_5014_; lean_object* v___x_5015_; 
v___x_5013_ = ((size_t)0ULL);
v___x_5014_ = lean_usize_of_nat(v___x_5004_);
v___x_5015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4999_, v_deps_5000_, v___x_5013_, v___x_5014_, v___x_5005_, v_a_5001_);
return v___x_5015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5016_, lean_object* v_deps_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5016_, v_deps_5017_, v_a_5018_);
lean_dec_ref(v_a_5018_);
lean_dec_ref(v_deps_5017_);
lean_dec(v_pkgEntries_5016_);
return v_res_5020_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_5021_, lean_object* v_x_5022_){
_start:
{
if (lean_obj_tag(v_x_5021_) == 0)
{
if (lean_obj_tag(v_x_5022_) == 0)
{
uint8_t v___x_5023_; 
v___x_5023_ = 1;
return v___x_5023_;
}
else
{
uint8_t v___x_5024_; 
v___x_5024_ = 0;
return v___x_5024_;
}
}
else
{
if (lean_obj_tag(v_x_5022_) == 0)
{
uint8_t v___x_5025_; 
v___x_5025_ = 0;
return v___x_5025_;
}
else
{
lean_object* v_val_5026_; lean_object* v_val_5027_; uint8_t v___x_5028_; 
v_val_5026_ = lean_ctor_get(v_x_5021_, 0);
v_val_5027_ = lean_ctor_get(v_x_5022_, 0);
v___x_5028_ = lean_string_dec_eq(v_val_5026_, v_val_5027_);
return v___x_5028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_5029_, lean_object* v_x_5030_){
_start:
{
uint8_t v_res_5031_; lean_object* v_r_5032_; 
v_res_5031_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5029_, v_x_5030_);
lean_dec(v_x_5030_);
lean_dec(v_x_5029_);
v_r_5032_ = lean_box(v_res_5031_);
return v_r_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(lean_object* v_pkg_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v_leanOpts_5041_, uint8_t v_reconfigure_5042_, lean_object* v_as_5043_, size_t v_i_5044_, size_t v_stop_5045_, lean_object* v_b_5046_, lean_object* v___y_5047_){
_start:
{
uint8_t v___x_5052_; 
v___x_5052_ = lean_usize_dec_eq(v_i_5044_, v_stop_5045_);
if (v___x_5052_ == 0)
{
lean_object* v_ws_5053_; lean_object* v_depIdxs_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5202_; 
v_ws_5053_ = lean_ctor_get(v_b_5046_, 0);
v_depIdxs_5054_ = lean_ctor_get(v_b_5046_, 1);
v_isSharedCheck_5202_ = !lean_is_exclusive(v_b_5046_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5056_ = v_b_5046_;
v_isShared_5057_ = v_isSharedCheck_5202_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_depIdxs_5054_);
lean_inc(v_ws_5053_);
lean_dec(v_b_5046_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5202_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v_lakeEnv_5058_; lean_object* v_packages_5059_; size_t v___x_5060_; size_t v___x_5061_; lean_object* v___x_5062_; lean_object* v___f_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_lakeEnv_5058_ = lean_ctor_get(v_ws_5053_, 0);
v_packages_5059_ = lean_ctor_get(v_ws_5053_, 4);
v___x_5060_ = ((size_t)1ULL);
v___x_5061_ = lean_usize_sub(v_i_5044_, v___x_5060_);
v___x_5062_ = lean_array_uget_borrowed(v_as_5043_, v___x_5061_);
lean_inc(v___x_5062_);
v___f_5063_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5063_, 0, v___x_5062_);
v___x_5064_ = lean_unsigned_to_nat(0u);
v___x_5065_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5063_, v_packages_5059_, v___x_5064_);
if (lean_obj_tag(v___x_5065_) == 1)
{
lean_object* v_val_5066_; lean_object* v___x_5067_; lean_object* v___x_5069_; 
v_val_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_val_5066_);
lean_dec_ref(v___x_5065_);
v___x_5067_ = lean_array_push(v_depIdxs_5054_, v_val_5066_);
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 1, v___x_5067_);
v___x_5069_ = v___x_5056_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_ws_5053_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
v_i_5044_ = v___x_5061_;
v_b_5046_ = v___x_5069_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5072_; lean_object* v_baseName_5073_; lean_object* v_name_5074_; lean_object* v_opts_5075_; uint8_t v___x_5076_; 
lean_inc_ref(v_packages_5059_);
lean_dec(v___x_5065_);
v_wsIdx_5072_ = lean_ctor_get(v_pkg_5038_, 0);
v_baseName_5073_ = lean_ctor_get(v_pkg_5038_, 1);
v_name_5074_ = lean_ctor_get(v___x_5062_, 0);
v_opts_5075_ = lean_ctor_get(v___x_5062_, 4);
v___x_5076_ = lean_name_eq(v_baseName_5073_, v_name_5074_);
if (v___x_5076_ == 0)
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5039_, v_name_5074_);
if (lean_obj_tag(v___x_5077_) == 1)
{
lean_object* v_val_5078_; lean_object* v___x_5079_; lean_object* v_dir_5080_; lean_object* v___x_5081_; 
v_val_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_val_5078_);
lean_dec_ref(v___x_5077_);
v___x_5079_ = lean_array_fget_borrowed(v_packages_5059_, v___x_5064_);
v_dir_5080_ = lean_ctor_get(v___x_5079_, 4);
lean_inc_ref(v___y_5040_);
lean_inc_ref(v_dir_5080_);
v___x_5081_ = l_Lake_PackageEntry_materialize(v_val_5078_, v_lakeEnv_5058_, v_dir_5080_, v___y_5040_, v___y_5047_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5156_; 
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5084_ = v___x_5081_;
v_isShared_5085_ = v_isSharedCheck_5156_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5081_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5156_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5086_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5041_);
lean_inc(v_opts_5075_);
v___x_5087_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5053_, v_a_5082_, v_opts_5075_, v_leanOpts_5041_, v_reconfigure_5042_, v___x_5086_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v_a_5089_; lean_object* v_wsIdx_5090_; lean_object* v___x_5091_; lean_object* v___x_5093_; 
lean_del_object(v___x_5084_);
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
v_a_5089_ = lean_ctor_get(v___x_5087_, 1);
lean_inc(v_a_5089_);
lean_dec_ref(v___x_5087_);
v_wsIdx_5090_ = lean_array_get_size(v_packages_5059_);
lean_dec_ref(v_packages_5059_);
v___x_5091_ = lean_array_push(v_depIdxs_5054_, v_wsIdx_5090_);
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 1, v___x_5091_);
lean_ctor_set(v___x_5056_, 0, v_a_5088_);
v___x_5093_ = v___x_5056_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5088_);
lean_ctor_set(v_reuseFailAlloc_5124_, 1, v___x_5091_);
v___x_5093_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
lean_object* v___x_5094_; uint8_t v___x_5095_; 
v___x_5094_ = lean_array_get_size(v_a_5089_);
v___x_5095_ = lean_nat_dec_lt(v___x_5064_, v___x_5094_);
if (v___x_5095_ == 0)
{
lean_dec(v_a_5089_);
v_i_5044_ = v___x_5061_;
v_b_5046_ = v___x_5093_;
goto _start;
}
else
{
lean_object* v___x_5097_; uint8_t v___x_5098_; 
v___x_5097_ = lean_box(0);
v___x_5098_ = lean_nat_dec_le(v___x_5094_, v___x_5094_);
if (v___x_5098_ == 0)
{
if (v___x_5095_ == 0)
{
lean_dec(v_a_5089_);
v_i_5044_ = v___x_5061_;
v_b_5046_ = v___x_5093_;
goto _start;
}
else
{
size_t v___x_5100_; size_t v___x_5101_; lean_object* v___x_5102_; 
v___x_5100_ = ((size_t)0ULL);
v___x_5101_ = lean_usize_of_nat(v___x_5094_);
v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5089_, v___x_5100_, v___x_5101_, v___x_5097_, v___y_5047_);
lean_dec(v_a_5089_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_dec_ref(v___x_5102_);
v_i_5044_ = v___x_5061_;
v_b_5046_ = v___x_5093_;
goto _start;
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec_ref(v___x_5093_);
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v_a_5104_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5102_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5102_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
}
else
{
size_t v___x_5112_; size_t v___x_5113_; lean_object* v___x_5114_; 
v___x_5112_ = ((size_t)0ULL);
v___x_5113_ = lean_usize_of_nat(v___x_5094_);
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5089_, v___x_5112_, v___x_5113_, v___x_5097_, v___y_5047_);
lean_dec(v_a_5089_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_dec_ref(v___x_5114_);
v_i_5044_ = v___x_5061_;
v_b_5046_ = v___x_5093_;
goto _start;
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec_ref(v___x_5093_);
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v_a_5116_ = lean_ctor_get(v___x_5114_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5114_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5114_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5126_; uint8_t v___x_5127_; 
lean_dec_ref(v_packages_5059_);
lean_del_object(v___x_5056_);
lean_dec_ref(v_depIdxs_5054_);
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v_a_5125_ = lean_ctor_get(v___x_5087_, 1);
lean_inc(v_a_5125_);
lean_dec_ref(v___x_5087_);
v___x_5126_ = lean_array_get_size(v_a_5125_);
v___x_5127_ = lean_nat_dec_lt(v___x_5064_, v___x_5126_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; lean_object* v___x_5130_; 
lean_dec(v_a_5125_);
v___x_5128_ = lean_box(0);
if (v_isShared_5085_ == 0)
{
lean_ctor_set_tag(v___x_5084_, 1);
lean_ctor_set(v___x_5084_, 0, v___x_5128_);
v___x_5130_ = v___x_5084_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5128_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
else
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
lean_del_object(v___x_5084_);
v___x_5132_ = lean_box(0);
v___x_5133_ = lean_nat_dec_le(v___x_5126_, v___x_5126_);
if (v___x_5133_ == 0)
{
if (v___x_5127_ == 0)
{
lean_dec(v_a_5125_);
goto v___jp_5049_;
}
else
{
size_t v___x_5134_; size_t v___x_5135_; lean_object* v___x_5136_; 
v___x_5134_ = ((size_t)0ULL);
v___x_5135_ = lean_usize_of_nat(v___x_5126_);
v___x_5136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5125_, v___x_5134_, v___x_5135_, v___x_5132_, v___y_5047_);
lean_dec(v_a_5125_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_dec_ref(v___x_5136_);
goto v___jp_5049_;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5136_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5136_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
}
else
{
size_t v___x_5145_; size_t v___x_5146_; lean_object* v___x_5147_; 
v___x_5145_ = ((size_t)0ULL);
v___x_5146_ = lean_usize_of_nat(v___x_5126_);
v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5125_, v___x_5145_, v___x_5146_, v___x_5132_, v___y_5047_);
lean_dec(v_a_5125_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_dec_ref(v___x_5147_);
goto v___jp_5049_;
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5147_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5147_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
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
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v_packages_5059_);
lean_del_object(v___x_5056_);
lean_dec_ref(v_depIdxs_5054_);
lean_dec_ref(v_ws_5053_);
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v_a_5157_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5081_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5081_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
else
{
uint8_t v___x_5165_; 
lean_inc(v_baseName_5073_);
lean_inc(v_wsIdx_5072_);
lean_dec(v___x_5077_);
lean_dec_ref(v_packages_5059_);
lean_del_object(v___x_5056_);
lean_dec_ref(v_depIdxs_5054_);
lean_dec_ref(v_ws_5053_);
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v___x_5165_ = lean_nat_dec_eq(v_wsIdx_5072_, v___x_5064_);
lean_dec(v_wsIdx_5072_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; uint8_t v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; uint8_t v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_5167_ = 1;
lean_inc(v_name_5074_);
v___x_5168_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5074_, v___x_5167_);
v___x_5169_ = lean_string_append(v___x_5166_, v___x_5168_);
lean_dec_ref(v___x_5168_);
v___x_5170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1));
v___x_5171_ = lean_string_append(v___x_5169_, v___x_5170_);
v___x_5172_ = l_Lean_Name_toString(v_baseName_5073_, v___x_5165_);
v___x_5173_ = lean_string_append(v___x_5171_, v___x_5172_);
lean_dec_ref(v___x_5172_);
v___x_5174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2));
v___x_5175_ = lean_string_append(v___x_5173_, v___x_5174_);
v___x_5176_ = 3;
v___x_5177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5177_, 0, v___x_5175_);
lean_ctor_set_uint8(v___x_5177_, sizeof(void*)*1, v___x_5176_);
lean_inc_ref(v___y_5047_);
v___x_5178_ = lean_apply_2(v___y_5047_, v___x_5177_, lean_box(0));
v___x_5179_ = lean_box(0);
v___x_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
return v___x_5180_;
}
else
{
lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; uint8_t v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
lean_dec(v_baseName_5073_);
v___x_5181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
lean_inc(v_name_5074_);
v___x_5182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5074_, v___x_5165_);
v___x_5183_ = lean_string_append(v___x_5181_, v___x_5182_);
v___x_5184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3));
v___x_5185_ = lean_string_append(v___x_5183_, v___x_5184_);
v___x_5186_ = lean_string_append(v___x_5185_, v___x_5182_);
lean_dec_ref(v___x_5182_);
v___x_5187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4));
v___x_5188_ = lean_string_append(v___x_5186_, v___x_5187_);
v___x_5189_ = 3;
v___x_5190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5190_, 0, v___x_5188_);
lean_ctor_set_uint8(v___x_5190_, sizeof(void*)*1, v___x_5189_);
lean_inc_ref(v___y_5047_);
v___x_5191_ = lean_apply_2(v___y_5047_, v___x_5190_, lean_box(0));
v___x_5192_ = lean_box(0);
v___x_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5192_);
return v___x_5193_;
}
}
}
else
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
lean_inc(v_baseName_5073_);
lean_dec_ref(v_packages_5059_);
lean_del_object(v___x_5056_);
lean_dec_ref(v_depIdxs_5054_);
lean_dec_ref(v_ws_5053_);
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v___x_5194_ = l_Lean_Name_toString(v_baseName_5073_, v___x_5052_);
v___x_5195_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_5196_ = lean_string_append(v___x_5194_, v___x_5195_);
v___x_5197_ = 3;
v___x_5198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5198_, 0, v___x_5196_);
lean_ctor_set_uint8(v___x_5198_, sizeof(void*)*1, v___x_5197_);
lean_inc_ref(v___y_5047_);
v___x_5199_ = lean_apply_2(v___y_5047_, v___x_5198_, lean_box(0));
v___x_5200_ = lean_box(0);
v___x_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
return v___x_5201_;
}
}
}
}
else
{
lean_object* v___x_5203_; 
lean_dec_ref(v_leanOpts_5041_);
lean_dec_ref(v___y_5040_);
lean_dec_ref(v_pkg_5038_);
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v_b_5046_);
return v___x_5203_;
}
v___jp_5049_:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = lean_box(0);
v___x_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
return v___x_5051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_pkg_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v_leanOpts_5207_, lean_object* v_reconfigure_5208_, lean_object* v_as_5209_, lean_object* v_i_5210_, lean_object* v_stop_5211_, lean_object* v_b_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
uint8_t v_reconfigure_boxed_5215_; size_t v_i_boxed_5216_; size_t v_stop_boxed_5217_; lean_object* v_res_5218_; 
v_reconfigure_boxed_5215_ = lean_unbox(v_reconfigure_5208_);
v_i_boxed_5216_ = lean_unbox_usize(v_i_5210_);
lean_dec(v_i_5210_);
v_stop_boxed_5217_ = lean_unbox_usize(v_stop_5211_);
lean_dec(v_stop_5211_);
v_res_5218_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5204_, v___y_5205_, v___y_5206_, v_leanOpts_5207_, v_reconfigure_boxed_5215_, v_as_5209_, v_i_boxed_5216_, v_stop_boxed_5217_, v_b_5212_, v___y_5213_);
lean_dec_ref(v___y_5213_);
lean_dec_ref(v_as_5209_);
lean_dec(v___y_5205_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object* v_start_5219_, lean_object* v_pkg_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v_leanOpts_5223_, uint8_t v_reconfigure_5224_, lean_object* v_as_5225_, size_t v_i_5226_, size_t v_stop_5227_, lean_object* v_b_5228_, lean_object* v___y_5229_){
_start:
{
uint8_t v___x_5234_; 
v___x_5234_ = lean_usize_dec_eq(v_i_5226_, v_stop_5227_);
if (v___x_5234_ == 0)
{
lean_object* v_ws_5235_; lean_object* v_depIdxs_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5384_; 
v_ws_5235_ = lean_ctor_get(v_b_5228_, 0);
v_depIdxs_5236_ = lean_ctor_get(v_b_5228_, 1);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_b_5228_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5238_ = v_b_5228_;
v_isShared_5239_ = v_isSharedCheck_5384_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_depIdxs_5236_);
lean_inc(v_ws_5235_);
lean_dec(v_b_5228_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5384_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v_lakeEnv_5240_; lean_object* v_packages_5241_; size_t v___x_5242_; size_t v___x_5243_; lean_object* v___x_5244_; lean_object* v___f_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v_lakeEnv_5240_ = lean_ctor_get(v_ws_5235_, 0);
v_packages_5241_ = lean_ctor_get(v_ws_5235_, 4);
v___x_5242_ = ((size_t)1ULL);
v___x_5243_ = lean_usize_sub(v_i_5226_, v___x_5242_);
v___x_5244_ = lean_array_uget_borrowed(v_as_5225_, v___x_5243_);
lean_inc(v___x_5244_);
v___f_5245_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5245_, 0, v___x_5244_);
v___x_5246_ = lean_unsigned_to_nat(0u);
v___x_5247_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5245_, v_packages_5241_, v___x_5246_);
if (lean_obj_tag(v___x_5247_) == 1)
{
lean_object* v_val_5248_; lean_object* v___x_5249_; lean_object* v___x_5251_; 
v_val_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_val_5248_);
lean_dec_ref(v___x_5247_);
v___x_5249_ = lean_array_push(v_depIdxs_5236_, v_val_5248_);
if (v_isShared_5239_ == 0)
{
lean_ctor_set(v___x_5238_, 1, v___x_5249_);
v___x_5251_ = v___x_5238_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_ws_5235_);
lean_ctor_set(v_reuseFailAlloc_5253_, 1, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
lean_object* v___x_5252_; 
v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5220_, v___y_5221_, v___y_5222_, v_leanOpts_5223_, v_reconfigure_5224_, v_as_5225_, v___x_5243_, v_stop_5227_, v___x_5251_, v___y_5229_);
return v___x_5252_;
}
}
else
{
lean_object* v_wsIdx_5254_; lean_object* v_baseName_5255_; lean_object* v_name_5256_; lean_object* v_opts_5257_; uint8_t v___x_5258_; 
lean_inc_ref(v_packages_5241_);
lean_dec(v___x_5247_);
v_wsIdx_5254_ = lean_ctor_get(v_pkg_5220_, 0);
v_baseName_5255_ = lean_ctor_get(v_pkg_5220_, 1);
v_name_5256_ = lean_ctor_get(v___x_5244_, 0);
v_opts_5257_ = lean_ctor_get(v___x_5244_, 4);
v___x_5258_ = lean_name_eq(v_baseName_5255_, v_name_5256_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
v___x_5259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5221_, v_name_5256_);
if (lean_obj_tag(v___x_5259_) == 1)
{
lean_object* v_val_5260_; lean_object* v___x_5261_; lean_object* v_dir_5262_; lean_object* v___x_5263_; 
v_val_5260_ = lean_ctor_get(v___x_5259_, 0);
lean_inc(v_val_5260_);
lean_dec_ref(v___x_5259_);
v___x_5261_ = lean_array_fget_borrowed(v_packages_5241_, v___x_5246_);
v_dir_5262_ = lean_ctor_get(v___x_5261_, 4);
lean_inc_ref(v___y_5222_);
lean_inc_ref(v_dir_5262_);
v___x_5263_ = l_Lake_PackageEntry_materialize(v_val_5260_, v_lakeEnv_5240_, v_dir_5262_, v___y_5222_, v___y_5229_);
if (lean_obj_tag(v___x_5263_) == 0)
{
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5338_; 
v_a_5264_ = lean_ctor_get(v___x_5263_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5266_ = v___x_5263_;
v_isShared_5267_ = v_isSharedCheck_5338_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v___x_5263_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5338_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5268_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5223_);
lean_inc(v_opts_5257_);
v___x_5269_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5235_, v_a_5264_, v_opts_5257_, v_leanOpts_5223_, v_reconfigure_5224_, v___x_5268_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v_a_5271_; lean_object* v_wsIdx_5272_; lean_object* v___x_5273_; lean_object* v___x_5275_; 
lean_del_object(v___x_5266_);
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5270_);
v_a_5271_ = lean_ctor_get(v___x_5269_, 1);
lean_inc(v_a_5271_);
lean_dec_ref(v___x_5269_);
v_wsIdx_5272_ = lean_array_get_size(v_packages_5241_);
lean_dec_ref(v_packages_5241_);
v___x_5273_ = lean_array_push(v_depIdxs_5236_, v_wsIdx_5272_);
if (v_isShared_5239_ == 0)
{
lean_ctor_set(v___x_5238_, 1, v___x_5273_);
lean_ctor_set(v___x_5238_, 0, v_a_5270_);
v___x_5275_ = v___x_5238_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5270_);
lean_ctor_set(v_reuseFailAlloc_5306_, 1, v___x_5273_);
v___x_5275_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5276_; uint8_t v___x_5277_; 
v___x_5276_ = lean_array_get_size(v_a_5271_);
v___x_5277_ = lean_nat_dec_lt(v___x_5246_, v___x_5276_);
if (v___x_5277_ == 0)
{
lean_object* v___x_5278_; 
lean_dec(v_a_5271_);
v___x_5278_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5220_, v___y_5221_, v___y_5222_, v_leanOpts_5223_, v_reconfigure_5224_, v_as_5225_, v___x_5243_, v_stop_5227_, v___x_5275_, v___y_5229_);
return v___x_5278_;
}
else
{
lean_object* v___x_5279_; uint8_t v___x_5280_; 
v___x_5279_ = lean_box(0);
v___x_5280_ = lean_nat_dec_le(v___x_5276_, v___x_5276_);
if (v___x_5280_ == 0)
{
if (v___x_5277_ == 0)
{
lean_object* v___x_5281_; 
lean_dec(v_a_5271_);
v___x_5281_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5220_, v___y_5221_, v___y_5222_, v_leanOpts_5223_, v_reconfigure_5224_, v_as_5225_, v___x_5243_, v_stop_5227_, v___x_5275_, v___y_5229_);
return v___x_5281_;
}
else
{
size_t v___x_5282_; size_t v___x_5283_; lean_object* v___x_5284_; 
v___x_5282_ = ((size_t)0ULL);
v___x_5283_ = lean_usize_of_nat(v___x_5276_);
v___x_5284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5271_, v___x_5282_, v___x_5283_, v___x_5279_, v___y_5229_);
lean_dec(v_a_5271_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v___x_5285_; 
lean_dec_ref(v___x_5284_);
v___x_5285_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5220_, v___y_5221_, v___y_5222_, v_leanOpts_5223_, v_reconfigure_5224_, v_as_5225_, v___x_5243_, v_stop_5227_, v___x_5275_, v___y_5229_);
return v___x_5285_;
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
lean_dec_ref(v___x_5275_);
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v_a_5286_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5284_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5284_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
}
else
{
size_t v___x_5294_; size_t v___x_5295_; lean_object* v___x_5296_; 
v___x_5294_ = ((size_t)0ULL);
v___x_5295_ = lean_usize_of_nat(v___x_5276_);
v___x_5296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5271_, v___x_5294_, v___x_5295_, v___x_5279_, v___y_5229_);
lean_dec(v_a_5271_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v___x_5297_; 
lean_dec_ref(v___x_5296_);
v___x_5297_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5220_, v___y_5221_, v___y_5222_, v_leanOpts_5223_, v_reconfigure_5224_, v_as_5225_, v___x_5243_, v_stop_5227_, v___x_5275_, v___y_5229_);
return v___x_5297_;
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
lean_dec_ref(v___x_5275_);
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v_a_5298_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5296_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5296_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5307_; lean_object* v___x_5308_; uint8_t v___x_5309_; 
lean_dec_ref(v_packages_5241_);
lean_del_object(v___x_5238_);
lean_dec_ref(v_depIdxs_5236_);
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v_a_5307_ = lean_ctor_get(v___x_5269_, 1);
lean_inc(v_a_5307_);
lean_dec_ref(v___x_5269_);
v___x_5308_ = lean_array_get_size(v_a_5307_);
v___x_5309_ = lean_nat_dec_lt(v___x_5246_, v___x_5308_);
if (v___x_5309_ == 0)
{
lean_object* v___x_5310_; lean_object* v___x_5312_; 
lean_dec(v_a_5307_);
v___x_5310_ = lean_box(0);
if (v_isShared_5267_ == 0)
{
lean_ctor_set_tag(v___x_5266_, 1);
lean_ctor_set(v___x_5266_, 0, v___x_5310_);
v___x_5312_ = v___x_5266_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5310_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
else
{
lean_object* v___x_5314_; uint8_t v___x_5315_; 
lean_del_object(v___x_5266_);
v___x_5314_ = lean_box(0);
v___x_5315_ = lean_nat_dec_le(v___x_5308_, v___x_5308_);
if (v___x_5315_ == 0)
{
if (v___x_5309_ == 0)
{
lean_dec(v_a_5307_);
goto v___jp_5231_;
}
else
{
size_t v___x_5316_; size_t v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = ((size_t)0ULL);
v___x_5317_ = lean_usize_of_nat(v___x_5308_);
v___x_5318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5307_, v___x_5316_, v___x_5317_, v___x_5314_, v___y_5229_);
lean_dec(v_a_5307_);
if (lean_obj_tag(v___x_5318_) == 0)
{
lean_dec_ref(v___x_5318_);
goto v___jp_5231_;
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
v_a_5319_ = lean_ctor_get(v___x_5318_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5318_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5318_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
}
else
{
size_t v___x_5327_; size_t v___x_5328_; lean_object* v___x_5329_; 
v___x_5327_ = ((size_t)0ULL);
v___x_5328_ = lean_usize_of_nat(v___x_5308_);
v___x_5329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5307_, v___x_5327_, v___x_5328_, v___x_5314_, v___y_5229_);
lean_dec(v_a_5307_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_dec_ref(v___x_5329_);
goto v___jp_5231_;
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5329_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5329_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
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
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_dec_ref(v_packages_5241_);
lean_del_object(v___x_5238_);
lean_dec_ref(v_depIdxs_5236_);
lean_dec_ref(v_ws_5235_);
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v_a_5339_ = lean_ctor_get(v___x_5263_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5263_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5263_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
else
{
uint8_t v___x_5347_; 
lean_inc(v_baseName_5255_);
lean_inc(v_wsIdx_5254_);
lean_dec(v___x_5259_);
lean_dec_ref(v_packages_5241_);
lean_del_object(v___x_5238_);
lean_dec_ref(v_depIdxs_5236_);
lean_dec_ref(v_ws_5235_);
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v___x_5347_ = lean_nat_dec_eq(v_wsIdx_5254_, v___x_5246_);
lean_dec(v_wsIdx_5254_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; uint8_t v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; uint8_t v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_5349_ = 1;
lean_inc(v_name_5256_);
v___x_5350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5256_, v___x_5349_);
v___x_5351_ = lean_string_append(v___x_5348_, v___x_5350_);
lean_dec_ref(v___x_5350_);
v___x_5352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1));
v___x_5353_ = lean_string_append(v___x_5351_, v___x_5352_);
v___x_5354_ = l_Lean_Name_toString(v_baseName_5255_, v___x_5347_);
v___x_5355_ = lean_string_append(v___x_5353_, v___x_5354_);
lean_dec_ref(v___x_5354_);
v___x_5356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2));
v___x_5357_ = lean_string_append(v___x_5355_, v___x_5356_);
v___x_5358_ = 3;
v___x_5359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5359_, 0, v___x_5357_);
lean_ctor_set_uint8(v___x_5359_, sizeof(void*)*1, v___x_5358_);
lean_inc_ref(v___y_5229_);
v___x_5360_ = lean_apply_2(v___y_5229_, v___x_5359_, lean_box(0));
v___x_5361_ = lean_box(0);
v___x_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5362_, 0, v___x_5361_);
return v___x_5362_;
}
else
{
lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; uint8_t v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
lean_dec(v_baseName_5255_);
v___x_5363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
lean_inc(v_name_5256_);
v___x_5364_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5256_, v___x_5347_);
v___x_5365_ = lean_string_append(v___x_5363_, v___x_5364_);
v___x_5366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3));
v___x_5367_ = lean_string_append(v___x_5365_, v___x_5366_);
v___x_5368_ = lean_string_append(v___x_5367_, v___x_5364_);
lean_dec_ref(v___x_5364_);
v___x_5369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4));
v___x_5370_ = lean_string_append(v___x_5368_, v___x_5369_);
v___x_5371_ = 3;
v___x_5372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5372_, 0, v___x_5370_);
lean_ctor_set_uint8(v___x_5372_, sizeof(void*)*1, v___x_5371_);
lean_inc_ref(v___y_5229_);
v___x_5373_ = lean_apply_2(v___y_5229_, v___x_5372_, lean_box(0));
v___x_5374_ = lean_box(0);
v___x_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
return v___x_5375_;
}
}
}
else
{
lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; uint8_t v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
lean_inc(v_baseName_5255_);
lean_dec_ref(v_packages_5241_);
lean_del_object(v___x_5238_);
lean_dec_ref(v_depIdxs_5236_);
lean_dec_ref(v_ws_5235_);
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v___x_5376_ = l_Lean_Name_toString(v_baseName_5255_, v___x_5234_);
v___x_5377_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_5378_ = lean_string_append(v___x_5376_, v___x_5377_);
v___x_5379_ = 3;
v___x_5380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5380_, 0, v___x_5378_);
lean_ctor_set_uint8(v___x_5380_, sizeof(void*)*1, v___x_5379_);
lean_inc_ref(v___y_5229_);
v___x_5381_ = lean_apply_2(v___y_5229_, v___x_5380_, lean_box(0));
v___x_5382_ = lean_box(0);
v___x_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5382_);
return v___x_5383_;
}
}
}
}
else
{
lean_object* v___x_5385_; 
lean_dec_ref(v_leanOpts_5223_);
lean_dec_ref(v___y_5222_);
lean_dec_ref(v_pkg_5220_);
v___x_5385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5385_, 0, v_b_5228_);
return v___x_5385_;
}
v___jp_5231_:
{
lean_object* v___x_5232_; lean_object* v___x_5233_; 
v___x_5232_ = lean_box(0);
v___x_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5232_);
return v___x_5233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object* v_start_5386_, lean_object* v_pkg_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v_leanOpts_5390_, lean_object* v_reconfigure_5391_, lean_object* v_as_5392_, lean_object* v_i_5393_, lean_object* v_stop_5394_, lean_object* v_b_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
uint8_t v_reconfigure_boxed_5398_; size_t v_i_boxed_5399_; size_t v_stop_boxed_5400_; lean_object* v_res_5401_; 
v_reconfigure_boxed_5398_ = lean_unbox(v_reconfigure_5391_);
v_i_boxed_5399_ = lean_unbox_usize(v_i_5393_);
lean_dec(v_i_5393_);
v_stop_boxed_5400_ = lean_unbox_usize(v_stop_5394_);
lean_dec(v_stop_5394_);
v_res_5401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_start_5386_, v_pkg_5387_, v___y_5388_, v___y_5389_, v_leanOpts_5390_, v_reconfigure_boxed_5398_, v_as_5392_, v_i_boxed_5399_, v_stop_boxed_5400_, v_b_5395_, v___y_5396_);
lean_dec_ref(v___y_5396_);
lean_dec_ref(v_as_5392_);
lean_dec(v___y_5388_);
lean_dec(v_start_5386_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v_leanOpts_5404_, uint8_t v_reconfigure_5405_, lean_object* v_ws_5406_, lean_object* v_wsIdx_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v_packages_5410_; lean_object* v_pkg_5411_; lean_object* v_depConfigs_5412_; lean_object* v_start_5413_; lean_object* v_ws_5415_; lean_object* v_packages_5416_; lean_object* v_depIdxs_5417_; lean_object* v___y_5418_; lean_object* v_____x_5434_; lean_object* v___y_5435_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v_s_5441_; lean_object* v___x_5442_; uint8_t v___x_5443_; 
v_packages_5410_ = lean_ctor_get(v_ws_5406_, 4);
v_pkg_5411_ = lean_array_fget(v_packages_5410_, v_wsIdx_5407_);
v_depConfigs_5412_ = lean_ctor_get(v_pkg_5411_, 12);
v_start_5413_ = lean_array_get_size(v_packages_5410_);
v___x_5439_ = lean_array_get_size(v_depConfigs_5412_);
v___x_5440_ = lean_mk_empty_array_with_capacity(v___x_5439_);
lean_inc_ref(v___x_5440_);
lean_inc_ref(v_ws_5406_);
v_s_5441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5441_, 0, v_ws_5406_);
lean_ctor_set(v_s_5441_, 1, v___x_5440_);
v___x_5442_ = lean_unsigned_to_nat(0u);
v___x_5443_ = lean_nat_dec_le(v___x_5439_, v___x_5439_);
if (v___x_5443_ == 0)
{
uint8_t v___x_5444_; 
v___x_5444_ = lean_nat_dec_lt(v___x_5442_, v___x_5439_);
if (v___x_5444_ == 0)
{
lean_object* v___x_5445_; 
lean_dec_ref(v_s_5441_);
v___x_5445_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_start_5413_, v___y_5402_, v___y_5403_, v_leanOpts_5404_, v_reconfigure_5405_, v_start_5413_, v_ws_5406_, v___y_5408_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5457_; 
v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5448_ = v___x_5445_;
v_isShared_5449_ = v_isSharedCheck_5457_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5445_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5457_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
size_t v_sz_5450_; size_t v___x_5451_; lean_object* v_depPkgs_5452_; lean_object* v_ws_5453_; lean_object* v___x_5455_; 
v_sz_5450_ = lean_array_size(v___x_5440_);
v___x_5451_ = ((size_t)0ULL);
v_depPkgs_5452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_a_5446_, v_sz_5450_, v___x_5451_, v___x_5440_);
v_ws_5453_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_a_5446_, v_pkg_5411_, v_depPkgs_5452_);
if (v_isShared_5449_ == 0)
{
lean_ctor_set(v___x_5448_, 0, v_ws_5453_);
v___x_5455_ = v___x_5448_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_ws_5453_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
else
{
lean_dec_ref(v___x_5440_);
lean_dec(v_pkg_5411_);
return v___x_5445_;
}
}
else
{
size_t v___x_5458_; size_t v___x_5459_; lean_object* v___x_5460_; 
lean_dec_ref(v___x_5440_);
lean_dec_ref(v_ws_5406_);
v___x_5458_ = lean_usize_of_nat(v___x_5439_);
v___x_5459_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5404_);
lean_inc_ref(v___y_5403_);
lean_inc(v_pkg_5411_);
v___x_5460_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_start_5413_, v_pkg_5411_, v___y_5402_, v___y_5403_, v_leanOpts_5404_, v_reconfigure_5405_, v_depConfigs_5412_, v___x_5458_, v___x_5459_, v_s_5441_, v___y_5408_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref(v___x_5460_);
v_____x_5434_ = v_a_5461_;
v___y_5435_ = v___y_5408_;
goto v___jp_5433_;
}
else
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5469_; 
lean_dec(v_pkg_5411_);
lean_dec_ref(v_leanOpts_5404_);
lean_dec_ref(v___y_5403_);
v_a_5462_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5464_ = v___x_5460_;
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5460_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
return v___x_5467_;
}
}
}
}
}
else
{
uint8_t v___x_5470_; 
lean_inc_ref(v_packages_5410_);
v___x_5470_ = lean_nat_dec_lt(v___x_5442_, v___x_5439_);
if (v___x_5470_ == 0)
{
lean_dec_ref(v_s_5441_);
v_ws_5415_ = v_ws_5406_;
v_packages_5416_ = v_packages_5410_;
v_depIdxs_5417_ = v___x_5440_;
v___y_5418_ = v___y_5408_;
goto v___jp_5414_;
}
else
{
size_t v___x_5471_; size_t v___x_5472_; lean_object* v___x_5473_; 
lean_dec_ref(v___x_5440_);
lean_dec_ref(v_packages_5410_);
lean_dec_ref(v_ws_5406_);
v___x_5471_ = lean_usize_of_nat(v___x_5439_);
v___x_5472_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5404_);
lean_inc_ref(v___y_5403_);
lean_inc(v_pkg_5411_);
v___x_5473_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_start_5413_, v_pkg_5411_, v___y_5402_, v___y_5403_, v_leanOpts_5404_, v_reconfigure_5405_, v_depConfigs_5412_, v___x_5471_, v___x_5472_, v_s_5441_, v___y_5408_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_a_5474_);
lean_dec_ref(v___x_5473_);
v_____x_5434_ = v_a_5474_;
v___y_5435_ = v___y_5408_;
goto v___jp_5433_;
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec(v_pkg_5411_);
lean_dec_ref(v_leanOpts_5404_);
lean_dec_ref(v___y_5403_);
v_a_5475_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5473_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5473_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
}
v___jp_5414_:
{
lean_object* v_stop_5419_; lean_object* v___x_5420_; 
v_stop_5419_ = lean_array_get_size(v_packages_5416_);
lean_dec_ref(v_packages_5416_);
v___x_5420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_stop_5419_, v___y_5402_, v___y_5403_, v_leanOpts_5404_, v_reconfigure_5405_, v_start_5413_, v_ws_5415_, v___y_5418_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5432_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5423_ = v___x_5420_;
v_isShared_5424_ = v_isSharedCheck_5432_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5420_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5432_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
size_t v_sz_5425_; size_t v___x_5426_; lean_object* v_depPkgs_5427_; lean_object* v_ws_5428_; lean_object* v___x_5430_; 
v_sz_5425_ = lean_array_size(v_depIdxs_5417_);
v___x_5426_ = ((size_t)0ULL);
v_depPkgs_5427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_a_5421_, v_sz_5425_, v___x_5426_, v_depIdxs_5417_);
v_ws_5428_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_a_5421_, v_pkg_5411_, v_depPkgs_5427_);
if (v_isShared_5424_ == 0)
{
lean_ctor_set(v___x_5423_, 0, v_ws_5428_);
v___x_5430_ = v___x_5423_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_ws_5428_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
else
{
lean_dec_ref(v_depIdxs_5417_);
lean_dec(v_pkg_5411_);
return v___x_5420_;
}
}
v___jp_5433_:
{
lean_object* v_ws_5436_; lean_object* v_depIdxs_5437_; lean_object* v_packages_5438_; 
v_ws_5436_ = lean_ctor_get(v_____x_5434_, 0);
lean_inc_ref(v_ws_5436_);
v_depIdxs_5437_ = lean_ctor_get(v_____x_5434_, 1);
lean_inc_ref(v_depIdxs_5437_);
lean_dec_ref(v_____x_5434_);
v_packages_5438_ = lean_ctor_get(v_ws_5436_, 4);
lean_inc_ref(v_packages_5438_);
v_ws_5415_ = v_ws_5436_;
v_packages_5416_ = v_packages_5438_;
v_depIdxs_5417_ = v_depIdxs_5437_;
v___y_5418_ = v___y_5435_;
goto v___jp_5414_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(lean_object* v_upperBound_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v_leanOpts_5486_, uint8_t v_reconfigure_5487_, lean_object* v_a_5488_, lean_object* v_b_5489_, lean_object* v___y_5490_){
_start:
{
uint8_t v___x_5492_; 
v___x_5492_ = lean_nat_dec_lt(v_a_5488_, v_upperBound_5483_);
if (v___x_5492_ == 0)
{
lean_object* v___x_5493_; 
lean_dec(v_a_5488_);
lean_dec_ref(v_leanOpts_5486_);
lean_dec_ref(v___y_5485_);
v___x_5493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5493_, 0, v_b_5489_);
return v___x_5493_;
}
else
{
lean_object* v___x_5494_; 
lean_inc_ref(v_leanOpts_5486_);
lean_inc_ref(v___y_5485_);
v___x_5494_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5484_, v___y_5485_, v_leanOpts_5486_, v_reconfigure_5487_, v_b_5489_, v_a_5488_, v___y_5490_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref(v___x_5494_);
v___x_5496_ = lean_unsigned_to_nat(1u);
v___x_5497_ = lean_nat_add(v_a_5488_, v___x_5496_);
lean_dec(v_a_5488_);
v_a_5488_ = v___x_5497_;
v_b_5489_ = v_a_5495_;
goto _start;
}
else
{
lean_dec(v_a_5488_);
lean_dec_ref(v_leanOpts_5486_);
lean_dec_ref(v___y_5485_);
return v___x_5494_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg___boxed(lean_object* v_upperBound_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v_leanOpts_5502_, lean_object* v_reconfigure_5503_, lean_object* v_a_5504_, lean_object* v_b_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_){
_start:
{
uint8_t v_reconfigure_boxed_5508_; lean_object* v_res_5509_; 
v_reconfigure_boxed_5508_ = lean_unbox(v_reconfigure_5503_);
v_res_5509_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_upperBound_5499_, v___y_5500_, v___y_5501_, v_leanOpts_5502_, v_reconfigure_boxed_5508_, v_a_5504_, v_b_5505_, v___y_5506_);
lean_dec_ref(v___y_5506_);
lean_dec(v___y_5500_);
lean_dec(v_upperBound_5499_);
return v_res_5509_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v_leanOpts_5512_, lean_object* v_reconfigure_5513_, lean_object* v_ws_5514_, lean_object* v_wsIdx_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_){
_start:
{
uint8_t v_reconfigure_boxed_5518_; lean_object* v_res_5519_; 
v_reconfigure_boxed_5518_ = lean_unbox(v_reconfigure_5513_);
v_res_5519_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5510_, v___y_5511_, v_leanOpts_5512_, v_reconfigure_boxed_5518_, v_ws_5514_, v_wsIdx_5515_, v___y_5516_);
lean_dec_ref(v___y_5516_);
lean_dec(v_wsIdx_5515_);
lean_dec(v___y_5510_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object* v_as_5520_, size_t v_i_5521_, size_t v_stop_5522_, lean_object* v_b_5523_){
_start:
{
uint8_t v___x_5524_; 
v___x_5524_ = lean_usize_dec_eq(v_i_5521_, v_stop_5522_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5525_; lean_object* v_name_5526_; lean_object* v___x_5527_; size_t v___x_5528_; size_t v___x_5529_; 
v___x_5525_ = lean_array_uget_borrowed(v_as_5520_, v_i_5521_);
v_name_5526_ = lean_ctor_get(v___x_5525_, 0);
lean_inc(v___x_5525_);
lean_inc(v_name_5526_);
v___x_5527_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5526_, v___x_5525_, v_b_5523_);
v___x_5528_ = ((size_t)1ULL);
v___x_5529_ = lean_usize_add(v_i_5521_, v___x_5528_);
v_i_5521_ = v___x_5529_;
v_b_5523_ = v___x_5527_;
goto _start;
}
else
{
return v_b_5523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object* v_as_5531_, lean_object* v_i_5532_, lean_object* v_stop_5533_, lean_object* v_b_5534_){
_start:
{
size_t v_i_boxed_5535_; size_t v_stop_boxed_5536_; lean_object* v_res_5537_; 
v_i_boxed_5535_ = lean_unbox_usize(v_i_5532_);
lean_dec(v_i_5532_);
v_stop_boxed_5536_ = lean_unbox_usize(v_stop_5533_);
lean_dec(v_stop_5533_);
v_res_5537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(v_as_5531_, v_i_boxed_5535_, v_stop_boxed_5536_, v_b_5534_);
lean_dec_ref(v_as_5531_);
return v_res_5537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5538_, size_t v_i_5539_, size_t v_stop_5540_, lean_object* v_b_5541_){
_start:
{
uint8_t v___x_5542_; 
v___x_5542_ = lean_usize_dec_eq(v_i_5539_, v_stop_5540_);
if (v___x_5542_ == 0)
{
lean_object* v___x_5543_; lean_object* v_name_5544_; lean_object* v___x_5545_; size_t v___x_5546_; size_t v___x_5547_; lean_object* v___x_5548_; 
v___x_5543_ = lean_array_uget_borrowed(v_as_5538_, v_i_5539_);
v_name_5544_ = lean_ctor_get(v___x_5543_, 0);
lean_inc(v___x_5543_);
lean_inc(v_name_5544_);
v___x_5545_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5544_, v___x_5543_, v_b_5541_);
v___x_5546_ = ((size_t)1ULL);
v___x_5547_ = lean_usize_add(v_i_5539_, v___x_5546_);
v___x_5548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(v_as_5538_, v___x_5547_, v_stop_5540_, v___x_5545_);
return v___x_5548_;
}
else
{
return v_b_5541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5549_, lean_object* v_i_5550_, lean_object* v_stop_5551_, lean_object* v_b_5552_){
_start:
{
size_t v_i_boxed_5553_; size_t v_stop_boxed_5554_; lean_object* v_res_5555_; 
v_i_boxed_5553_ = lean_unbox_usize(v_i_5550_);
lean_dec(v_i_5550_);
v_stop_boxed_5554_ = lean_unbox_usize(v_stop_5551_);
lean_dec(v_stop_5551_);
v_res_5555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5549_, v_i_boxed_5553_, v_stop_boxed_5554_, v_b_5552_);
lean_dec_ref(v_as_5549_);
return v_res_5555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5565_, lean_object* v_manifest_5566_, lean_object* v_leanOpts_5567_, uint8_t v_reconfigure_5568_, lean_object* v_overrides_5569_, lean_object* v_a_5570_){
_start:
{
lean_object* v___y_5573_; lean_object* v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5622_; lean_object* v___y_5623_; lean_object* v___y_5624_; lean_object* v___y_5625_; lean_object* v_packagesDir_x3f_5667_; lean_object* v_packages_5668_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5684_; lean_object* v___x_5692_; lean_object* v___x_5693_; uint8_t v___x_5694_; 
v_packagesDir_x3f_5667_ = lean_ctor_get(v_manifest_5566_, 2);
lean_inc(v_packagesDir_x3f_5667_);
v_packages_5668_ = lean_ctor_get(v_manifest_5566_, 3);
lean_inc_ref(v_packages_5668_);
lean_dec_ref(v_manifest_5566_);
v___x_5692_ = lean_array_get_size(v_packages_5668_);
v___x_5693_ = lean_unsigned_to_nat(0u);
v___x_5694_ = lean_nat_dec_eq(v___x_5692_, v___x_5693_);
if (v___x_5694_ == 0)
{
lean_object* v_packages_5695_; lean_object* v___x_5696_; lean_object* v_config_5697_; lean_object* v_toWorkspaceConfig_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; uint8_t v___x_5702_; 
v_packages_5695_ = lean_ctor_get(v_ws_5565_, 4);
v___x_5696_ = lean_array_fget_borrowed(v_packages_5695_, v___x_5693_);
v_config_5697_ = lean_ctor_get(v___x_5696_, 6);
v_toWorkspaceConfig_5698_ = lean_ctor_get(v_config_5697_, 0);
lean_inc_ref(v_toWorkspaceConfig_5698_);
v___x_5699_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5698_);
v___x_5700_ = l_Lake_mkRelPathString(v___x_5699_);
v___x_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
v___x_5702_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5667_, v___x_5701_);
lean_dec_ref(v___x_5701_);
if (v___x_5702_ == 0)
{
lean_object* v___x_5703_; lean_object* v___x_5704_; 
v___x_5703_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5570_);
v___x_5704_ = lean_apply_2(v_a_5570_, v___x_5703_, lean_box(0));
v___y_5684_ = v_a_5570_;
goto v___jp_5683_;
}
else
{
v___y_5684_ = v_a_5570_;
goto v___jp_5683_;
}
}
else
{
v___y_5684_ = v_a_5570_;
goto v___jp_5683_;
}
v___jp_5572_:
{
lean_object* v___x_5577_; 
v___x_5577_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5573_, v___y_5575_, v_leanOpts_5567_, v_reconfigure_5568_, v_ws_5565_, v___y_5574_, v___y_5576_);
lean_dec(v___y_5573_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5585_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5580_ = v___x_5577_;
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v___x_5577_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
else
{
lean_object* v_a_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5593_; 
v_a_5586_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5577_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5577_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5591_; 
if (v_isShared_5589_ == 0)
{
v___x_5591_ = v___x_5588_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5586_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
}
v___jp_5594_:
{
if (lean_obj_tag(v___y_5599_) == 0)
{
lean_dec_ref(v___y_5595_);
v___y_5573_ = v___y_5599_;
v___y_5574_ = v___y_5596_;
v___y_5575_ = v___y_5597_;
v___y_5576_ = v___y_5598_;
goto v___jp_5572_;
}
else
{
lean_object* v___x_5600_; uint8_t v___x_5601_; 
v___x_5600_ = lean_array_get_size(v___y_5595_);
lean_dec_ref(v___y_5595_);
v___x_5601_ = lean_nat_dec_eq(v___x_5600_, v___y_5596_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; 
lean_dec_ref(v___y_5597_);
lean_dec_ref(v_leanOpts_5567_);
lean_dec_ref(v_ws_5565_);
v___x_5602_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5598_);
v___x_5603_ = lean_apply_2(v___y_5598_, v___x_5602_, lean_box(0));
v___x_5604_ = lean_box(0);
v___x_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
return v___x_5605_;
}
else
{
v___y_5573_ = v___y_5599_;
v___y_5574_ = v___y_5596_;
v___y_5575_ = v___y_5597_;
v___y_5576_ = v___y_5598_;
goto v___jp_5572_;
}
}
}
v___jp_5606_:
{
lean_object* v___x_5612_; uint8_t v___x_5613_; 
v___x_5612_ = lean_array_get_size(v_overrides_5569_);
v___x_5613_ = lean_nat_dec_lt(v___y_5608_, v___x_5612_);
if (v___x_5613_ == 0)
{
v___y_5595_ = v___y_5607_;
v___y_5596_ = v___y_5608_;
v___y_5597_ = v___y_5609_;
v___y_5598_ = v___y_5610_;
v___y_5599_ = v___y_5611_;
goto v___jp_5594_;
}
else
{
uint8_t v___x_5614_; 
v___x_5614_ = lean_nat_dec_le(v___x_5612_, v___x_5612_);
if (v___x_5614_ == 0)
{
if (v___x_5613_ == 0)
{
v___y_5595_ = v___y_5607_;
v___y_5596_ = v___y_5608_;
v___y_5597_ = v___y_5609_;
v___y_5598_ = v___y_5610_;
v___y_5599_ = v___y_5611_;
goto v___jp_5594_;
}
else
{
size_t v___x_5615_; size_t v___x_5616_; lean_object* v___x_5617_; 
v___x_5615_ = ((size_t)0ULL);
v___x_5616_ = lean_usize_of_nat(v___x_5612_);
v___x_5617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5569_, v___x_5615_, v___x_5616_, v___y_5611_);
v___y_5595_ = v___y_5607_;
v___y_5596_ = v___y_5608_;
v___y_5597_ = v___y_5609_;
v___y_5598_ = v___y_5610_;
v___y_5599_ = v___x_5617_;
goto v___jp_5594_;
}
}
else
{
size_t v___x_5618_; size_t v___x_5619_; lean_object* v___x_5620_; 
v___x_5618_ = ((size_t)0ULL);
v___x_5619_ = lean_usize_of_nat(v___x_5612_);
v___x_5620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5569_, v___x_5618_, v___x_5619_, v___y_5611_);
v___y_5595_ = v___y_5607_;
v___y_5596_ = v___y_5608_;
v___y_5597_ = v___y_5609_;
v___y_5598_ = v___y_5610_;
v___y_5599_ = v___x_5620_;
goto v___jp_5594_;
}
}
}
v___jp_5621_:
{
lean_object* v_packages_5626_; lean_object* v___x_5627_; lean_object* v_dir_5628_; lean_object* v_depConfigs_5629_; lean_object* v___x_5630_; 
v_packages_5626_ = lean_ctor_get(v_ws_5565_, 4);
v___x_5627_ = lean_array_fget_borrowed(v_packages_5626_, v___y_5622_);
v_dir_5628_ = lean_ctor_get(v___x_5627_, 4);
v_depConfigs_5629_ = lean_ctor_get(v___x_5627_, 12);
v___x_5630_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5625_, v_depConfigs_5629_, v___y_5624_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
lean_dec_ref(v___x_5630_);
v___x_5631_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5628_);
v___x_5632_ = l_Lake_joinRelative(v_dir_5628_, v___x_5631_);
v___x_5633_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5634_ = l_Lake_joinRelative(v___x_5632_, v___x_5633_);
v___x_5635_ = l_Lake_Manifest_tryLoadEntries(v___x_5634_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_a_5636_; lean_object* v___x_5637_; uint8_t v___x_5638_; 
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_a_5636_);
lean_dec_ref(v___x_5635_);
v___x_5637_ = lean_array_get_size(v_a_5636_);
v___x_5638_ = lean_nat_dec_lt(v___y_5622_, v___x_5637_);
if (v___x_5638_ == 0)
{
lean_dec(v_a_5636_);
lean_inc_ref(v_depConfigs_5629_);
v___y_5607_ = v_depConfigs_5629_;
v___y_5608_ = v___y_5622_;
v___y_5609_ = v___y_5623_;
v___y_5610_ = v___y_5624_;
v___y_5611_ = v___y_5625_;
goto v___jp_5606_;
}
else
{
uint8_t v___x_5639_; 
v___x_5639_ = lean_nat_dec_le(v___x_5637_, v___x_5637_);
if (v___x_5639_ == 0)
{
if (v___x_5638_ == 0)
{
lean_dec(v_a_5636_);
lean_inc_ref(v_depConfigs_5629_);
v___y_5607_ = v_depConfigs_5629_;
v___y_5608_ = v___y_5622_;
v___y_5609_ = v___y_5623_;
v___y_5610_ = v___y_5624_;
v___y_5611_ = v___y_5625_;
goto v___jp_5606_;
}
else
{
size_t v___x_5640_; size_t v___x_5641_; lean_object* v___x_5642_; 
v___x_5640_ = ((size_t)0ULL);
v___x_5641_ = lean_usize_of_nat(v___x_5637_);
v___x_5642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5636_, v___x_5640_, v___x_5641_, v___y_5625_);
lean_dec(v_a_5636_);
lean_inc_ref(v_depConfigs_5629_);
v___y_5607_ = v_depConfigs_5629_;
v___y_5608_ = v___y_5622_;
v___y_5609_ = v___y_5623_;
v___y_5610_ = v___y_5624_;
v___y_5611_ = v___x_5642_;
goto v___jp_5606_;
}
}
else
{
size_t v___x_5643_; size_t v___x_5644_; lean_object* v___x_5645_; 
v___x_5643_ = ((size_t)0ULL);
v___x_5644_ = lean_usize_of_nat(v___x_5637_);
v___x_5645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5636_, v___x_5643_, v___x_5644_, v___y_5625_);
lean_dec(v_a_5636_);
lean_inc_ref(v_depConfigs_5629_);
v___y_5607_ = v_depConfigs_5629_;
v___y_5608_ = v___y_5622_;
v___y_5609_ = v___y_5623_;
v___y_5610_ = v___y_5624_;
v___y_5611_ = v___x_5645_;
goto v___jp_5606_;
}
}
}
else
{
lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5658_; 
lean_dec(v___y_5625_);
lean_dec_ref(v___y_5623_);
lean_dec_ref(v_leanOpts_5567_);
lean_dec_ref(v_ws_5565_);
v_a_5646_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5648_ = v___x_5635_;
v_isShared_5649_ = v_isSharedCheck_5658_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_dec(v___x_5635_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5658_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5650_; uint8_t v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5656_; 
v___x_5650_ = lean_io_error_to_string(v_a_5646_);
v___x_5651_ = 3;
v___x_5652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5652_, 0, v___x_5650_);
lean_ctor_set_uint8(v___x_5652_, sizeof(void*)*1, v___x_5651_);
lean_inc_ref(v___y_5624_);
v___x_5653_ = lean_apply_2(v___y_5624_, v___x_5652_, lean_box(0));
v___x_5654_ = lean_box(0);
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 0, v___x_5654_);
v___x_5656_ = v___x_5648_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v___x_5654_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
lean_dec(v___y_5625_);
lean_dec_ref(v___y_5623_);
lean_dec_ref(v_leanOpts_5567_);
lean_dec_ref(v_ws_5565_);
v_a_5659_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5630_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5630_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
v___jp_5669_:
{
lean_object* v_pkgEntries_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; uint8_t v___x_5675_; 
v_pkgEntries_5672_ = lean_box(1);
v___x_5673_ = lean_unsigned_to_nat(0u);
v___x_5674_ = lean_array_get_size(v_packages_5668_);
v___x_5675_ = lean_nat_dec_lt(v___x_5673_, v___x_5674_);
if (v___x_5675_ == 0)
{
lean_dec_ref(v_packages_5668_);
v___y_5622_ = v___x_5673_;
v___y_5623_ = v___y_5671_;
v___y_5624_ = v___y_5670_;
v___y_5625_ = v_pkgEntries_5672_;
goto v___jp_5621_;
}
else
{
uint8_t v___x_5676_; 
v___x_5676_ = lean_nat_dec_le(v___x_5674_, v___x_5674_);
if (v___x_5676_ == 0)
{
if (v___x_5675_ == 0)
{
lean_dec_ref(v_packages_5668_);
v___y_5622_ = v___x_5673_;
v___y_5623_ = v___y_5671_;
v___y_5624_ = v___y_5670_;
v___y_5625_ = v_pkgEntries_5672_;
goto v___jp_5621_;
}
else
{
size_t v___x_5677_; size_t v___x_5678_; lean_object* v___x_5679_; 
v___x_5677_ = ((size_t)0ULL);
v___x_5678_ = lean_usize_of_nat(v___x_5674_);
v___x_5679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5668_, v___x_5677_, v___x_5678_, v_pkgEntries_5672_);
lean_dec_ref(v_packages_5668_);
v___y_5622_ = v___x_5673_;
v___y_5623_ = v___y_5671_;
v___y_5624_ = v___y_5670_;
v___y_5625_ = v___x_5679_;
goto v___jp_5621_;
}
}
else
{
size_t v___x_5680_; size_t v___x_5681_; lean_object* v___x_5682_; 
v___x_5680_ = ((size_t)0ULL);
v___x_5681_ = lean_usize_of_nat(v___x_5674_);
v___x_5682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5668_, v___x_5680_, v___x_5681_, v_pkgEntries_5672_);
lean_dec_ref(v_packages_5668_);
v___y_5622_ = v___x_5673_;
v___y_5623_ = v___y_5671_;
v___y_5624_ = v___y_5670_;
v___y_5625_ = v___x_5682_;
goto v___jp_5621_;
}
}
}
v___jp_5683_:
{
if (lean_obj_tag(v_packagesDir_x3f_5667_) == 0)
{
lean_object* v_packages_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v_config_5688_; lean_object* v_toWorkspaceConfig_5689_; lean_object* v___x_5690_; 
v_packages_5685_ = lean_ctor_get(v_ws_5565_, 4);
v___x_5686_ = lean_unsigned_to_nat(0u);
v___x_5687_ = lean_array_fget_borrowed(v_packages_5685_, v___x_5686_);
v_config_5688_ = lean_ctor_get(v___x_5687_, 6);
v_toWorkspaceConfig_5689_ = lean_ctor_get(v_config_5688_, 0);
lean_inc_ref(v_toWorkspaceConfig_5689_);
v___x_5690_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5689_);
v___y_5670_ = v___y_5684_;
v___y_5671_ = v___x_5690_;
goto v___jp_5669_;
}
else
{
lean_object* v_val_5691_; 
v_val_5691_ = lean_ctor_get(v_packagesDir_x3f_5667_, 0);
lean_inc(v_val_5691_);
lean_dec_ref(v_packagesDir_x3f_5667_);
v___y_5670_ = v___y_5684_;
v___y_5671_ = v_val_5691_;
goto v___jp_5669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5705_, lean_object* v_manifest_5706_, lean_object* v_leanOpts_5707_, lean_object* v_reconfigure_5708_, lean_object* v_overrides_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
uint8_t v_reconfigure_boxed_5712_; lean_object* v_res_5713_; 
v_reconfigure_boxed_5712_ = lean_unbox(v_reconfigure_5708_);
v_res_5713_ = l_Lake_Workspace_materializeDeps(v_ws_5705_, v_manifest_5706_, v_leanOpts_5707_, v_reconfigure_boxed_5712_, v_overrides_5709_, v_a_5710_);
lean_dec_ref(v_a_5710_);
lean_dec_ref(v_overrides_5709_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v_leanOpts_5716_, uint8_t v_reconfigure_5717_, lean_object* v_ws_5718_, lean_object* v_wsIdx_5719_, lean_object* v_h_5720_, lean_object* v___y_5721_){
_start:
{
lean_object* v___x_5723_; 
v___x_5723_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5714_, v___y_5715_, v_leanOpts_5716_, v_reconfigure_5717_, v_ws_5718_, v_wsIdx_5719_, v___y_5721_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v_leanOpts_5726_, lean_object* v_reconfigure_5727_, lean_object* v_ws_5728_, lean_object* v_wsIdx_5729_, lean_object* v_h_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
uint8_t v_reconfigure_boxed_5733_; lean_object* v_res_5734_; 
v_reconfigure_boxed_5733_ = lean_unbox(v_reconfigure_5727_);
v_res_5734_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5724_, v___y_5725_, v_leanOpts_5726_, v_reconfigure_boxed_5733_, v_ws_5728_, v_wsIdx_5729_, v_h_5730_, v___y_5731_);
lean_dec_ref(v___y_5731_);
lean_dec(v_wsIdx_5729_);
lean_dec(v___y_5724_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_upperBound_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v_leanOpts_5738_, uint8_t v_reconfigure_5739_, lean_object* v_inst_5740_, lean_object* v_R_5741_, lean_object* v_a_5742_, lean_object* v_b_5743_, lean_object* v_c_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v___x_5747_; 
v___x_5747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_upperBound_5735_, v___y_5736_, v___y_5737_, v_leanOpts_5738_, v_reconfigure_5739_, v_a_5742_, v_b_5743_, v___y_5745_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_upperBound_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v_leanOpts_5751_, lean_object* v_reconfigure_5752_, lean_object* v_inst_5753_, lean_object* v_R_5754_, lean_object* v_a_5755_, lean_object* v_b_5756_, lean_object* v_c_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_){
_start:
{
uint8_t v_reconfigure_boxed_5760_; lean_object* v_res_5761_; 
v_reconfigure_boxed_5760_ = lean_unbox(v_reconfigure_5752_);
v_res_5761_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_upperBound_5748_, v___y_5749_, v___y_5750_, v_leanOpts_5751_, v_reconfigure_boxed_5760_, v_inst_5753_, v_R_5754_, v_a_5755_, v_b_5756_, v_c_5757_, v___y_5758_);
lean_dec_ref(v___y_5758_);
lean_dec(v___y_5749_);
lean_dec(v_upperBound_5748_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3(lean_object* v_start_5762_, lean_object* v_pkg_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v_leanOpts_5766_, uint8_t v_reconfigure_5767_, lean_object* v_as_5768_, size_t v_i_5769_, size_t v_stop_5770_, lean_object* v_b_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v___x_5774_; 
v___x_5774_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5763_, v___y_5764_, v___y_5765_, v_leanOpts_5766_, v_reconfigure_5767_, v_as_5768_, v_i_5769_, v_stop_5770_, v_b_5771_, v___y_5772_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___boxed(lean_object* v_start_5775_, lean_object* v_pkg_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v_leanOpts_5779_, lean_object* v_reconfigure_5780_, lean_object* v_as_5781_, lean_object* v_i_5782_, lean_object* v_stop_5783_, lean_object* v_b_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_){
_start:
{
uint8_t v_reconfigure_boxed_5787_; size_t v_i_boxed_5788_; size_t v_stop_boxed_5789_; lean_object* v_res_5790_; 
v_reconfigure_boxed_5787_ = lean_unbox(v_reconfigure_5780_);
v_i_boxed_5788_ = lean_unbox_usize(v_i_5782_);
lean_dec(v_i_5782_);
v_stop_boxed_5789_ = lean_unbox_usize(v_stop_5783_);
lean_dec(v_stop_5783_);
v_res_5790_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3(v_start_5775_, v_pkg_5776_, v___y_5777_, v___y_5778_, v_leanOpts_5779_, v_reconfigure_boxed_5787_, v_as_5781_, v_i_boxed_5788_, v_stop_boxed_5789_, v_b_5784_, v___y_5785_);
lean_dec_ref(v___y_5785_);
lean_dec_ref(v_as_5781_);
lean_dec(v___y_5777_);
lean_dec(v_start_5775_);
return v_res_5790_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_StoreInsts(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Load_Resolve_0__Lake_restartCode = _init_l___private_Lake_Load_Resolve_0__Lake_restartCode();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Load_Materialize(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Lean_Runtime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Resolve(builtin);
}
#ifdef __cplusplus
}
#endif

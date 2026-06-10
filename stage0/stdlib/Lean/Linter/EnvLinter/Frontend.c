// Lean compiler output
// Module: Lean.Linter.EnvLinter.Frontend
// Imports: public import Lean.Linter.EnvLinter.Basic public import Lean.Linter.Init import Lean.DeclarationRange import Lean.Util.Path import Lean.CoreM import Lean.Elab.Command
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Elab_Command_mkMetaContext;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_EnvLinter_envLinterExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Environment_const2ModIdx(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Linter.EnvLinter.LintVerbosity.low"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Linter.EnvLinter.LintVerbosity.medium"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Linter.EnvLinter.LintVerbosity.high"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6;
static lean_once_cell_t l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value;
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_EnvLinter_getEnvLinters___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_EnvLinter_getEnvLinters___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_getEnvLinters___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinters___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_isLinterEnabledFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isLinterEnabledFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LINTER FAILED:\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "#check "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__1;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " /- "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " -/"};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__4_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__5;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__6_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__7;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ": error: "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__8_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__9;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__10_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__11;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarnings___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarnings___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-- "};
static const lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1;
static const lean_string_object l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "/- The `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` linter reports:\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -/\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "/- OK: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__1;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " declarations (plus "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " automatically generated ones) "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__5;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__7;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " linters\n\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__9;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-- Found "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__11;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " error"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__12 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__13;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__14 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(lean_object* v_low_28_){
_start:
{
lean_inc(v_low_28_);
return v_low_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg___boxed(lean_object* v_low_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(v_low_29_);
lean_dec(v_low_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_low_34_){
_start:
{
lean_inc(v_low_34_);
return v_low_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_low_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_low_38_);
lean_dec(v_low_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(lean_object* v_medium_41_){
_start:
{
lean_inc(v_medium_41_);
return v_medium_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg___boxed(lean_object* v_medium_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(v_medium_42_);
lean_dec(v_medium_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_medium_47_){
_start:
{
lean_inc(v_medium_47_);
return v_medium_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_medium_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_medium_51_);
lean_dec(v_medium_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(lean_object* v_high_54_){
_start:
{
lean_inc(v_high_54_);
return v_high_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg___boxed(lean_object* v_high_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(v_high_55_);
lean_dec(v_high_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_high_60_){
_start:
{
lean_inc(v_high_60_);
return v_high_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_high_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_high_64_);
lean_dec(v_high_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ofNat___boxed(lean_object* v_n_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(v_n_77_);
lean_dec(v_n_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_80_);
v___x_83_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity___boxed(lean_object* v_x_85_, lean_object* v_y_86_){
_start:
{
uint8_t v_x_13__boxed_87_; uint8_t v_y_14__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_13__boxed_87_ = lean_unbox(v_x_85_);
v_y_14__boxed_88_ = lean_unbox(v_y_86_);
v_res_89_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_x_13__boxed_87_, v_y_14__boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(uint8_t v_x_104_, lean_object* v_prec_105_){
_start:
{
lean_object* v___y_107_; lean_object* v___y_114_; lean_object* v___y_121_; 
switch(v_x_104_)
{
case 0:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_105_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_107_ = v___x_129_;
goto v___jp_106_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_107_ = v___x_130_;
goto v___jp_106_;
}
}
case 1:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_105_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_114_ = v___x_133_;
goto v___jp_113_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_114_ = v___x_134_;
goto v___jp_113_;
}
}
default: 
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_prec_105_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_121_ = v___x_137_;
goto v___jp_120_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_121_ = v___x_138_;
goto v___jp_120_;
}
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1));
lean_inc(v___y_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_105_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_105_);
return v___x_119_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_105_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed(lean_object* v_x_139_, lean_object* v_prec_140_){
_start:
{
uint8_t v_x_177__boxed_141_; lean_object* v_res_142_; 
v_x_177__boxed_141_ = lean_unbox(v_x_139_);
v_res_142_ = l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(v_x_177__boxed_141_, v_prec_140_);
lean_dec(v_prec_140_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(lean_object* v_x1_145_, lean_object* v_x2_146_){
_start:
{
lean_object* v_optName_147_; lean_object* v_optName_148_; uint8_t v___x_149_; 
v_optName_147_ = lean_ctor_get(v_x1_145_, 1);
v_optName_148_ = lean_ctor_get(v_x2_146_, 1);
v___x_149_ = l_Lean_Name_lt(v_optName_147_, v_optName_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0___boxed(lean_object* v_x1_150_, lean_object* v_x2_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v_x1_150_, v_x2_151_);
lean_dec_ref(v_x2_151_);
lean_dec_ref(v_x1_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(lean_object* v_a_154_, lean_object* v_as_155_, lean_object* v_k_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_mid_161_; lean_object* v_midVal_162_; uint8_t v___x_163_; 
v___x_159_ = lean_nat_add(v_x_157_, v_x_158_);
v___x_160_ = lean_unsigned_to_nat(1u);
v_mid_161_ = lean_nat_shiftr(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
v_midVal_162_ = lean_array_fget_borrowed(v_as_155_, v_mid_161_);
v___x_163_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v_midVal_162_, v_k_156_);
if (v___x_163_ == 0)
{
uint8_t v___x_164_; 
lean_dec(v_x_158_);
v___x_164_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v_k_156_, v_midVal_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
lean_dec(v_x_157_);
v___x_165_ = lean_array_get_size(v_as_155_);
v___x_166_ = lean_nat_dec_lt(v_mid_161_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_mid_161_);
lean_dec_ref(v_a_154_);
return v_as_155_;
}
else
{
lean_object* v___x_167_; lean_object* v_xs_x27_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v_xs_x27_168_ = lean_array_fset(v_as_155_, v_mid_161_, v___x_167_);
v___x_169_ = lean_array_fset(v_xs_x27_168_, v_mid_161_, v_a_154_);
lean_dec(v_mid_161_);
return v___x_169_;
}
}
else
{
v_x_158_ = v_mid_161_;
goto _start;
}
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_mid_161_, v_x_157_);
if (v___x_171_ == 0)
{
lean_dec(v_x_157_);
v_x_157_ = v_mid_161_;
goto _start;
}
else
{
lean_object* v___x_173_; lean_object* v_j_174_; lean_object* v_as_175_; lean_object* v___x_176_; 
lean_dec(v_mid_161_);
lean_dec(v_x_158_);
v___x_173_ = lean_nat_add(v_x_157_, v___x_160_);
lean_dec(v_x_157_);
v_j_174_ = lean_array_get_size(v_as_155_);
v_as_175_ = lean_array_push(v_as_155_, v_a_154_);
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_173_, v_as_175_, v_j_174_);
lean_dec(v___x_173_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg___boxed(lean_object* v_a_177_, lean_object* v_as_178_, lean_object* v_k_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(v_a_177_, v_as_178_, v_k_179_, v_x_180_, v_x_181_);
lean_dec_ref(v_k_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0(lean_object* v_a_183_, lean_object* v_as_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_array_get_size(v_as_184_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_nat_dec_eq(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_array_fget_borrowed(v_as_184_, v___x_187_);
v___x_190_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v_k_185_, v___x_189_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; 
v___x_191_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v___x_189_, v_k_185_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_lt(v___x_187_, v___x_186_);
if (v___x_192_ == 0)
{
lean_dec_ref(v_a_183_);
return v_as_184_;
}
else
{
lean_object* v___x_193_; lean_object* v_xs_x27_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v_xs_x27_194_ = lean_array_fset(v_as_184_, v___x_187_, v___x_193_);
v___x_195_ = lean_array_fset(v_xs_x27_194_, v___x_187_, v_a_183_);
return v___x_195_;
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_sub(v___x_186_, v___x_196_);
v___x_198_ = lean_array_fget_borrowed(v_as_184_, v___x_197_);
v___x_199_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v___x_198_, v_k_185_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v_k_185_, v___x_198_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_lt(v___x_197_, v___x_186_);
if (v___x_201_ == 0)
{
lean_dec(v___x_197_);
lean_dec_ref(v_a_183_);
return v_as_184_;
}
else
{
lean_object* v___x_202_; lean_object* v_xs_x27_203_; lean_object* v___x_204_; 
v___x_202_ = lean_box(0);
v_xs_x27_203_ = lean_array_fset(v_as_184_, v___x_197_, v___x_202_);
v___x_204_ = lean_array_fset(v_xs_x27_203_, v___x_197_, v_a_183_);
lean_dec(v___x_197_);
return v___x_204_;
}
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(v_a_183_, v_as_184_, v_k_185_, v___x_187_, v___x_197_);
return v___x_205_;
}
}
else
{
lean_object* v___x_206_; 
lean_dec(v___x_197_);
v___x_206_ = lean_array_push(v_as_184_, v_a_183_);
return v___x_206_;
}
}
}
else
{
lean_object* v_as_207_; lean_object* v___x_208_; 
v_as_207_ = lean_array_push(v_as_184_, v_a_183_);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_187_, v_as_207_, v___x_186_);
return v___x_208_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_array_push(v_as_184_, v_a_183_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___boxed(lean_object* v_a_210_, lean_object* v_as_211_, lean_object* v_k_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0(v_a_210_, v_as_211_, v_k_212_);
lean_dec_ref(v_k_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(lean_object* v_opts_x3f_214_, lean_object* v_init_215_, lean_object* v_x_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_d_221_; 
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_k_224_; lean_object* v_v_225_; lean_object* v_l_226_; lean_object* v_r_227_; lean_object* v___x_228_; 
v_k_224_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_k_224_);
v_v_225_ = lean_ctor_get(v_x_216_, 2);
lean_inc(v_v_225_);
v_l_226_ = lean_ctor_get(v_x_216_, 3);
lean_inc(v_l_226_);
v_r_227_ = lean_ctor_get(v_x_216_, 4);
lean_inc(v_r_227_);
lean_dec_ref_known(v_x_216_, 5);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(v_opts_x3f_214_, v_init_215_, v_l_226_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
if (lean_obj_tag(v_a_229_) == 0)
{
lean_object* v_a_230_; 
lean_dec_ref_known(v___x_228_, 1);
lean_dec(v_r_227_);
lean_dec(v_v_225_);
lean_dec(v_k_224_);
v_a_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v_a_229_, 1);
v_d_221_ = v_a_230_;
goto v___jp_220_;
}
else
{
lean_object* v_a_231_; 
v_a_231_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v_a_229_, 1);
if (lean_obj_tag(v_opts_x3f_214_) == 0)
{
lean_dec_ref_known(v___x_228_, 1);
goto v___jp_232_;
}
else
{
lean_object* v_val_245_; uint8_t v___x_246_; 
v_val_245_ = lean_ctor_get(v_opts_x3f_214_, 0);
v___x_246_ = l_Lean_Linter_isLinterEnabledByOptions(v_k_224_, v_val_245_);
if (v___x_246_ == 0)
{
lean_dec(v_a_231_);
lean_dec(v_v_225_);
lean_dec(v_k_224_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_247_; 
v_a_247_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_228_, 1);
if (lean_obj_tag(v_a_247_) == 0)
{
lean_object* v_a_248_; 
lean_dec(v_r_227_);
v_a_248_ = lean_ctor_get(v_a_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v_a_247_, 1);
v_d_221_ = v_a_248_;
goto v___jp_220_;
}
else
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v_a_247_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v_a_247_, 1);
v_init_215_ = v_a_249_;
v_x_216_ = v_r_227_;
goto _start;
}
}
else
{
lean_dec(v_r_227_);
return v___x_228_;
}
}
else
{
lean_dec_ref_known(v___x_228_, 1);
goto v___jp_232_;
}
}
v___jp_232_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_k_224_, v_v_225_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_n(v_a_234_, 2);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0(v_a_234_, v_a_231_, v_a_234_);
lean_dec(v_a_234_);
v_init_215_ = v___x_235_;
v_x_216_ = v_r_227_;
goto _start;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_a_231_);
lean_dec(v_r_227_);
v_a_237_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_233_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_233_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
else
{
lean_dec(v_r_227_);
lean_dec(v_v_225_);
lean_dec(v_k_224_);
return v___x_228_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_init_215_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v_d_221_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1___boxed(lean_object* v_opts_x3f_253_, lean_object* v_init_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(v_opts_x3f_253_, v_init_254_, v_x_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_opts_x3f_253_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object* v_opts_x3f_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_266_; lean_object* v_env_267_; lean_object* v___x_268_; lean_object* v_toEnvExtension_269_; lean_object* v_asyncMode_270_; lean_object* v___x_271_; lean_object* v_result_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_266_ = lean_st_ref_get(v_a_264_);
v_env_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc_ref(v_env_267_);
lean_dec(v___x_266_);
v___x_268_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_269_ = lean_ctor_get(v___x_268_, 0);
v_asyncMode_270_ = lean_ctor_get(v_toEnvExtension_269_, 2);
v___x_271_ = lean_box(1);
v_result_272_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getEnvLinters___closed__0));
v___x_273_ = lean_box(0);
v___x_274_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_271_, v___x_268_, v_env_267_, v_asyncMode_270_, v___x_273_);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(v_opts_x3f_262_, v_result_272_, v___x_274_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_284_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_a_280_; lean_object* v___x_282_; 
v_a_280_ = lean_ctor_get(v_a_276_, 0);
lean_inc(v_a_280_);
lean_dec(v_a_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v_a_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_275_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinters___boxed(lean_object* v_opts_x3f_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Linter_EnvLinter_getEnvLinters(v_opts_x3f_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_opts_x3f_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0(lean_object* v_a_298_, lean_object* v_as_299_, lean_object* v_k_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(v_a_298_, v_as_299_, v_k_300_, v_x_301_, v_x_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___boxed(lean_object* v_a_306_, lean_object* v_as_307_, lean_object* v_k_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0(v_a_306_, v_as_307_, v_k_308_, v_x_309_, v_x_310_, v_x_311_, v_x_312_);
lean_dec_ref(v_k_308_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_isLinterEnabledFor(lean_object* v_env_314_, lean_object* v_linter_315_, lean_object* v_decl_316_){
_start:
{
lean_object* v_optName_317_; lean_object* v___x_318_; 
v_optName_317_ = lean_ctor_get(v_linter_315_, 1);
v___x_318_ = l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(v_env_314_, v_decl_316_, v_optName_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
else
{
lean_object* v_val_320_; uint8_t v___x_321_; 
v_val_320_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_318_, 1);
v___x_321_ = lean_unbox(v_val_320_);
lean_dec(v_val_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isLinterEnabledFor___boxed(lean_object* v_env_322_, lean_object* v_linter_323_, lean_object* v_decl_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Lean_Linter_EnvLinter_isLinterEnabledFor(v_env_322_, v_linter_323_, v_decl_324_);
lean_dec_ref(v_linter_323_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object* v___x_327_, lean_object* v_linter_328_, lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
lean_object* v___y_334_; uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_339_);
lean_inc_ref(v___x_327_);
v___x_340_ = l_Lean_Linter_EnvLinter_isLinterEnabledFor(v___x_327_, v_linter_328_, v___x_339_);
if (v___x_340_ == 0)
{
v___y_334_ = v_b_332_;
goto v___jp_333_;
}
else
{
lean_object* v___x_341_; 
lean_inc(v___x_339_);
v___x_341_ = lean_array_push(v_b_332_, v___x_339_);
v___y_334_ = v___x_341_;
goto v___jp_333_;
}
}
else
{
lean_dec_ref(v___x_327_);
return v_b_332_;
}
v___jp_333_:
{
size_t v___x_335_; size_t v___x_336_; 
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_330_, v___x_335_);
v_i_330_ = v___x_336_;
v_b_332_ = v___y_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object* v___x_342_, lean_object* v_linter_343_, lean_object* v_as_344_, lean_object* v_i_345_, lean_object* v_stop_346_, lean_object* v_b_347_){
_start:
{
size_t v_i_boxed_348_; size_t v_stop_boxed_349_; lean_object* v_res_350_; 
v_i_boxed_348_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_stop_boxed_349_ = lean_unbox_usize(v_stop_346_);
lean_dec(v_stop_346_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_342_, v_linter_343_, v_as_344_, v_i_boxed_348_, v_stop_boxed_349_, v_b_347_);
lean_dec_ref(v_as_344_);
lean_dec_ref(v_linter_343_);
return v_res_350_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_351_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_355_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
lean_ctor_set(v___x_355_, 4, v___x_354_);
lean_ctor_set(v___x_355_, 5, v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_unsigned_to_nat(32u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
lean_ctor_set(v___x_360_, 3, v___x_359_);
lean_ctor_set(v___x_360_, 4, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object* v___x_361_, lean_object* v___x_362_, lean_object* v_test_363_, lean_object* v_v_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; size_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
lean_inc_n(v___x_361_, 5);
v___x_370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_370_, 0, v___x_361_);
lean_ctor_set(v___x_370_, 1, v___x_361_);
lean_ctor_set(v___x_370_, 2, v___x_361_);
lean_ctor_set(v___x_370_, 3, v___x_361_);
lean_ctor_set(v___x_370_, 4, v___x_369_);
lean_ctor_set(v___x_370_, 5, v___x_369_);
lean_ctor_set(v___x_370_, 6, v___x_369_);
lean_ctor_set(v___x_370_, 7, v___x_369_);
lean_ctor_set(v___x_370_, 8, v___x_369_);
lean_ctor_set(v___x_370_, 9, v___x_369_);
v___x_371_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2);
v___x_372_ = lean_unsigned_to_nat(32u);
v___x_373_ = lean_mk_empty_array_with_capacity(v___x_372_);
v___x_374_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3);
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_373_);
lean_ctor_set(v___x_376_, 2, v___x_361_);
lean_ctor_set(v___x_376_, 3, v___x_361_);
lean_ctor_set_usize(v___x_376_, 4, v___x_375_);
v___x_377_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4);
v___x_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_378_, 0, v___x_370_);
lean_ctor_set(v___x_378_, 1, v___x_371_);
lean_ctor_set(v___x_378_, 2, v___x_362_);
lean_ctor_set(v___x_378_, 3, v___x_376_);
lean_ctor_set(v___x_378_, 4, v___x_377_);
v___x_379_ = lean_st_mk_ref(v___x_378_);
v___x_380_ = l_Lean_Elab_Command_mkMetaContext;
lean_inc(v___y_367_);
lean_inc_ref(v___y_366_);
lean_inc(v___x_379_);
v___x_381_ = lean_apply_6(v_test_363_, v_v_364_, v___x_380_, v___x_379_, v___y_366_, v___y_367_, lean_box(0));
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_st_ref_get(v___x_379_);
lean_dec(v___x_379_);
lean_dec(v___x_386_);
if (v_isShared_385_ == 0)
{
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_382_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_dec(v___x_379_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object* v___x_391_, lean_object* v___x_392_, lean_object* v_test_393_, lean_object* v_v_394_, lean_object* v_x_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(v___x_391_, v___x_392_, v_test_393_, v_v_394_, v_x_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object* v_a_400_, lean_object* v___x_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_apply_2(v_a_400_, v___x_401_, lean_box(0));
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_403_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_403_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object* v_a_420_, lean_object* v___x_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(v_a_420_, v___x_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object* v_linter_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_bs_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec_ref(v_linter_424_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_bs_427_);
return v___x_432_;
}
else
{
lean_object* v_toEnvLinter_433_; lean_object* v_test_434_; lean_object* v_v_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_toEnvLinter_433_ = lean_ctor_get(v_linter_424_, 0);
v_test_434_ = lean_ctor_get(v_toEnvLinter_433_, 0);
v_v_435_ = lean_array_uget(v_bs_427_, v_i_426_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_box(1);
lean_inc(v_v_435_);
lean_inc_ref(v_test_434_);
v___f_438_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed), 8, 4);
lean_closure_set(v___f_438_, 0, v___x_436_);
lean_closure_set(v___f_438_, 1, v___x_437_);
lean_closure_set(v___f_438_, 2, v_test_434_);
lean_closure_set(v___f_438_, 3, v_v_435_);
v___x_439_ = lean_box(0);
v___x_440_ = l_Lean_Core_wrapAsync___redArg(v___f_438_, v___x_439_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; lean_object* v_bs_x27_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = lean_box(0);
v___f_443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_443_, 0, v_a_441_);
lean_closure_set(v___f_443_, 1, v___x_442_);
v___x_444_ = lean_io_as_task(v___f_443_, v___x_436_);
v_bs_x27_445_ = lean_array_uset(v_bs_427_, v_i_426_, v___x_436_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_v_435_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_426_, v___x_447_);
v___x_449_ = lean_array_uset(v_bs_x27_445_, v_i_426_, v___x_446_);
v_i_426_ = v___x_448_;
v_bs_427_ = v___x_449_;
goto _start;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_v_435_);
lean_dec_ref(v_bs_427_);
lean_dec_ref(v_linter_424_);
v_a_451_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_440_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_440_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object* v_linter_459_, lean_object* v_sz_460_, lean_object* v_i_461_, lean_object* v_bs_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
size_t v_sz_boxed_466_; size_t v_i_boxed_467_; lean_object* v_res_468_; 
v_sz_boxed_466_ = lean_unbox_usize(v_sz_460_);
lean_dec(v_sz_460_);
v_i_boxed_467_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_linter_459_, v_sz_boxed_466_, v_i_boxed_467_, v_bs_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(lean_object* v_decls_471_, lean_object* v___x_472_, size_t v_sz_473_, size_t v_i_474_, lean_object* v_bs_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v___x_472_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v_bs_475_);
return v___x_480_;
}
else
{
lean_object* v_v_481_; lean_object* v___x_482_; lean_object* v_bs_x27_483_; lean_object* v___y_485_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_v_481_ = lean_array_uget(v_bs_475_, v_i_474_);
v___x_482_ = lean_unsigned_to_nat(0u);
v_bs_x27_483_ = lean_array_uset(v_bs_475_, v_i_474_, v___x_482_);
v___x_495_ = lean_array_get_size(v_decls_471_);
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_497_ = lean_nat_dec_lt(v___x_482_, v___x_495_);
if (v___x_497_ == 0)
{
v___y_485_ = v___x_496_;
goto v___jp_484_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = lean_nat_dec_le(v___x_495_, v___x_495_);
if (v___x_498_ == 0)
{
if (v___x_497_ == 0)
{
v___y_485_ = v___x_496_;
goto v___jp_484_;
}
else
{
size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((size_t)0ULL);
v___x_500_ = lean_usize_of_nat(v___x_495_);
lean_inc_ref(v___x_472_);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_472_, v_v_481_, v_decls_471_, v___x_499_, v___x_500_, v___x_496_);
v___y_485_ = v___x_501_;
goto v___jp_484_;
}
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = ((size_t)0ULL);
v___x_503_ = lean_usize_of_nat(v___x_495_);
lean_inc_ref(v___x_472_);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_472_, v_v_481_, v_decls_471_, v___x_502_, v___x_503_, v___x_496_);
v___y_485_ = v___x_504_;
goto v___jp_484_;
}
}
v___jp_484_:
{
size_t v_sz_486_; size_t v___x_487_; lean_object* v___x_488_; 
v_sz_486_ = lean_array_size(v___y_485_);
v___x_487_ = ((size_t)0ULL);
lean_inc(v_v_481_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_481_, v_sz_486_, v___x_487_, v___y_485_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_v_481_);
lean_ctor_set(v___x_490_, 1, v_a_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_474_, v___x_491_);
v___x_493_ = lean_array_uset(v_bs_x27_483_, v_i_474_, v___x_490_);
v_i_474_ = v___x_492_;
v_bs_475_ = v___x_493_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_483_);
lean_dec(v_v_481_);
lean_dec_ref(v___x_472_);
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___boxed(lean_object* v_decls_505_, lean_object* v___x_506_, lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_bs_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
size_t v_sz_boxed_513_; size_t v_i_boxed_514_; lean_object* v_res_515_; 
v_sz_boxed_513_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_514_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(v_decls_505_, v___x_506_, v_sz_boxed_513_, v_i_boxed_514_, v_bs_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v_decls_505_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object* v___x_516_, lean_object* v_decls_517_, size_t v_sz_518_, size_t v_i_519_, lean_object* v_bs_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_lt(v_i_519_, v_sz_518_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v___x_516_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_bs_520_);
return v___x_525_;
}
else
{
lean_object* v_v_526_; lean_object* v___x_527_; lean_object* v_bs_x27_528_; lean_object* v___y_530_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_v_526_ = lean_array_uget(v_bs_520_, v_i_519_);
v___x_527_ = lean_unsigned_to_nat(0u);
v_bs_x27_528_ = lean_array_uset(v_bs_520_, v_i_519_, v___x_527_);
v___x_540_ = lean_array_get_size(v_decls_517_);
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_542_ = lean_nat_dec_lt(v___x_527_, v___x_540_);
if (v___x_542_ == 0)
{
v___y_530_ = v___x_541_;
goto v___jp_529_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = lean_nat_dec_le(v___x_540_, v___x_540_);
if (v___x_543_ == 0)
{
if (v___x_542_ == 0)
{
v___y_530_ = v___x_541_;
goto v___jp_529_;
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_540_);
lean_inc_ref(v___x_516_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_516_, v_v_526_, v_decls_517_, v___x_544_, v___x_545_, v___x_541_);
v___y_530_ = v___x_546_;
goto v___jp_529_;
}
}
else
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_540_);
lean_inc_ref(v___x_516_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_516_, v_v_526_, v_decls_517_, v___x_547_, v___x_548_, v___x_541_);
v___y_530_ = v___x_549_;
goto v___jp_529_;
}
}
v___jp_529_:
{
size_t v_sz_531_; size_t v___x_532_; lean_object* v___x_533_; 
v_sz_531_ = lean_array_size(v___y_530_);
v___x_532_ = ((size_t)0ULL);
lean_inc(v_v_526_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_526_, v_sz_531_, v___x_532_, v___y_530_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_v_526_);
lean_ctor_set(v___x_535_, 1, v_a_534_);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_add(v_i_519_, v___x_536_);
v___x_538_ = lean_array_uset(v_bs_x27_528_, v_i_519_, v___x_535_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(v_decls_517_, v___x_516_, v_sz_518_, v___x_537_, v___x_538_, v___y_521_, v___y_522_);
return v___x_539_;
}
else
{
lean_dec_ref(v_bs_x27_528_);
lean_dec(v_v_526_);
lean_dec_ref(v___x_516_);
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object* v___x_550_, lean_object* v_decls_551_, lean_object* v_sz_552_, lean_object* v_i_553_, lean_object* v_bs_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_552_);
lean_dec(v_sz_552_);
v_i_boxed_559_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v___x_550_, v_decls_551_, v_sz_boxed_558_, v_i_boxed_559_, v_bs_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v_decls_551_);
return v_res_560_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_561_; uint64_t v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(1723u);
v___x_562_ = lean_uint64_of_nat(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
return v_x_563_;
}
else
{
lean_object* v_key_565_; lean_object* v_value_566_; lean_object* v_tail_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_593_; 
v_key_565_ = lean_ctor_get(v_x_564_, 0);
v_value_566_ = lean_ctor_get(v_x_564_, 1);
v_tail_567_ = lean_ctor_get(v_x_564_, 2);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_593_ == 0)
{
v___x_569_ = v_x_564_;
v_isShared_570_ = v_isSharedCheck_593_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_tail_567_);
lean_inc(v_value_566_);
lean_inc(v_key_565_);
lean_dec(v_x_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_593_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; uint64_t v___y_573_; 
v___x_571_ = lean_array_get_size(v_x_563_);
if (lean_obj_tag(v_key_565_) == 0)
{
uint64_t v___x_591_; 
v___x_591_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_573_ = v___x_591_;
goto v___jp_572_;
}
else
{
uint64_t v_hash_592_; 
v_hash_592_ = lean_ctor_get_uint64(v_key_565_, sizeof(void*)*2);
v___y_573_ = v_hash_592_;
goto v___jp_572_;
}
v___jp_572_:
{
uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v_fold_576_; uint64_t v___x_577_; uint64_t v___x_578_; uint64_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_574_ = 32ULL;
v___x_575_ = lean_uint64_shift_right(v___y_573_, v___x_574_);
v_fold_576_ = lean_uint64_xor(v___y_573_, v___x_575_);
v___x_577_ = 16ULL;
v___x_578_ = lean_uint64_shift_right(v_fold_576_, v___x_577_);
v___x_579_ = lean_uint64_xor(v_fold_576_, v___x_578_);
v___x_580_ = lean_uint64_to_usize(v___x_579_);
v___x_581_ = lean_usize_of_nat(v___x_571_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_sub(v___x_581_, v___x_582_);
v___x_584_ = lean_usize_land(v___x_580_, v___x_583_);
v___x_585_ = lean_array_uget_borrowed(v_x_563_, v___x_584_);
lean_inc(v___x_585_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_585_);
v___x_587_ = v___x_569_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_key_565_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_value_566_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v___x_585_);
v___x_587_ = v_reuseFailAlloc_590_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = lean_array_uset(v_x_563_, v___x_584_, v___x_587_);
v_x_563_ = v___x_588_;
v_x_564_ = v_tail_567_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_594_, lean_object* v_source_595_, lean_object* v_target_596_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_size(v_source_595_);
v___x_598_ = lean_nat_dec_lt(v_i_594_, v___x_597_);
if (v___x_598_ == 0)
{
lean_dec_ref(v_source_595_);
lean_dec(v_i_594_);
return v_target_596_;
}
else
{
lean_object* v_es_599_; lean_object* v___x_600_; lean_object* v_source_601_; lean_object* v_target_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_es_599_ = lean_array_fget(v_source_595_, v_i_594_);
v___x_600_ = lean_box(0);
v_source_601_ = lean_array_fset(v_source_595_, v_i_594_, v___x_600_);
v_target_602_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(v_target_596_, v_es_599_);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_i_594_, v___x_603_);
lean_dec(v_i_594_);
v_i_594_ = v___x_604_;
v_source_595_ = v_source_601_;
v_target_596_ = v_target_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object* v_data_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_nbuckets_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_607_ = lean_array_get_size(v_data_606_);
v___x_608_ = lean_unsigned_to_nat(2u);
v_nbuckets_609_ = lean_nat_mul(v___x_607_, v___x_608_);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_box(0);
v___x_612_ = lean_mk_array(v_nbuckets_609_, v___x_611_);
v___x_613_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v___x_610_, v_data_606_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_dec(v_b_615_);
lean_dec(v_a_614_);
return v_x_616_;
}
else
{
lean_object* v_key_617_; lean_object* v_value_618_; lean_object* v_tail_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_631_; 
v_key_617_ = lean_ctor_get(v_x_616_, 0);
v_value_618_ = lean_ctor_get(v_x_616_, 1);
v_tail_619_ = lean_ctor_get(v_x_616_, 2);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_631_ == 0)
{
v___x_621_ = v_x_616_;
v_isShared_622_ = v_isSharedCheck_631_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_tail_619_);
lean_inc(v_value_618_);
lean_inc(v_key_617_);
lean_dec(v_x_616_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_631_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; 
v___x_623_ = lean_name_eq(v_key_617_, v_a_614_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_614_, v_b_615_, v_tail_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 2, v___x_624_);
v___x_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_key_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_value_618_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v___x_629_; 
lean_dec(v_value_618_);
lean_dec(v_key_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_b_615_);
lean_ctor_set(v___x_621_, 0, v_a_614_);
v___x_629_ = v___x_621_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_614_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_b_615_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_tail_619_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object* v_a_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
uint8_t v___x_634_; 
v___x_634_ = 0;
return v___x_634_;
}
else
{
lean_object* v_key_635_; lean_object* v_tail_636_; uint8_t v___x_637_; 
v_key_635_ = lean_ctor_get(v_x_633_, 0);
v_tail_636_ = lean_ctor_get(v_x_633_, 2);
v___x_637_ = lean_name_eq(v_key_635_, v_a_632_);
if (v___x_637_ == 0)
{
v_x_633_ = v_tail_636_;
goto _start;
}
else
{
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_639_, v_x_640_);
lean_dec(v_x_640_);
lean_dec(v_a_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object* v_m_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
lean_object* v_size_646_; lean_object* v_buckets_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_693_; 
v_size_646_ = lean_ctor_get(v_m_643_, 0);
v_buckets_647_ = lean_ctor_get(v_m_643_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_m_643_);
if (v_isSharedCheck_693_ == 0)
{
v___x_649_ = v_m_643_;
v_isShared_650_ = v_isSharedCheck_693_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_buckets_647_);
lean_inc(v_size_646_);
lean_dec(v_m_643_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_693_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; uint64_t v___y_653_; 
v___x_651_ = lean_array_get_size(v_buckets_647_);
if (lean_obj_tag(v_a_644_) == 0)
{
uint64_t v___x_691_; 
v___x_691_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_653_ = v___x_691_;
goto v___jp_652_;
}
else
{
uint64_t v_hash_692_; 
v_hash_692_ = lean_ctor_get_uint64(v_a_644_, sizeof(void*)*2);
v___y_653_ = v_hash_692_;
goto v___jp_652_;
}
v___jp_652_:
{
uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v_fold_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v_bkt_665_; uint8_t v___x_666_; 
v___x_654_ = 32ULL;
v___x_655_ = lean_uint64_shift_right(v___y_653_, v___x_654_);
v_fold_656_ = lean_uint64_xor(v___y_653_, v___x_655_);
v___x_657_ = 16ULL;
v___x_658_ = lean_uint64_shift_right(v_fold_656_, v___x_657_);
v___x_659_ = lean_uint64_xor(v_fold_656_, v___x_658_);
v___x_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = lean_usize_of_nat(v___x_651_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_sub(v___x_661_, v___x_662_);
v___x_664_ = lean_usize_land(v___x_660_, v___x_663_);
v_bkt_665_ = lean_array_uget_borrowed(v_buckets_647_, v___x_664_);
v___x_666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_644_, v_bkt_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v_size_x27_668_; lean_object* v___x_669_; lean_object* v_buckets_x27_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v_size_x27_668_ = lean_nat_add(v_size_646_, v___x_667_);
lean_dec(v_size_646_);
lean_inc(v_bkt_665_);
v___x_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_669_, 0, v_a_644_);
lean_ctor_set(v___x_669_, 1, v_b_645_);
lean_ctor_set(v___x_669_, 2, v_bkt_665_);
v_buckets_x27_670_ = lean_array_uset(v_buckets_647_, v___x_664_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(4u);
v___x_672_ = lean_nat_mul(v_size_x27_668_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(3u);
v___x_674_ = lean_nat_div(v___x_672_, v___x_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_array_get_size(v_buckets_x27_670_);
v___x_676_ = lean_nat_dec_le(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v_val_677_; lean_object* v___x_679_; 
v_val_677_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_buckets_x27_670_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_val_677_);
lean_ctor_set(v___x_649_, 0, v_size_x27_668_);
v___x_679_ = v___x_649_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_size_x27_668_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_val_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v___x_682_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_buckets_x27_670_);
lean_ctor_set(v___x_649_, 0, v_size_x27_668_);
v___x_682_ = v___x_649_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_size_x27_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_buckets_x27_670_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
lean_object* v___x_684_; lean_object* v_buckets_x27_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
lean_inc(v_bkt_665_);
v___x_684_ = lean_box(0);
v_buckets_x27_685_ = lean_array_uset(v_buckets_647_, v___x_664_, v___x_684_);
v___x_686_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_644_, v_b_645_, v_bkt_665_);
v___x_687_ = lean_array_uset(v_buckets_x27_685_, v___x_664_, v___x_686_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_687_);
v___x_689_ = v___x_649_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_size_646_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object* v_as_697_, size_t v_sz_698_, size_t v_i_699_, lean_object* v_b_700_){
_start:
{
lean_object* v_a_703_; uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_b_700_);
return v___x_708_;
}
else
{
lean_object* v_a_709_; lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_727_; 
v_a_709_ = lean_array_uget(v_as_697_, v_i_699_);
v_fst_710_ = lean_ctor_get(v_a_709_, 0);
v_snd_711_ = lean_ctor_get(v_a_709_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_727_ == 0)
{
v___x_713_ = v_a_709_;
v_isShared_714_ = v_isSharedCheck_727_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_a_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_727_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_val_716_; lean_object* v___x_718_; 
v___x_718_ = lean_task_get_own(v_snd_711_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1);
v___x_721_ = l_Lean_Exception_toMessageData(v_a_719_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 7);
lean_ctor_set(v___x_713_, 1, v___x_721_);
lean_ctor_set(v___x_713_, 0, v___x_720_);
v___x_723_ = v___x_713_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v_val_716_ = v___x_723_;
goto v___jp_715_;
}
}
else
{
lean_object* v_a_725_; 
lean_del_object(v___x_713_);
v_a_725_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_718_, 1);
if (lean_obj_tag(v_a_725_) == 1)
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v_a_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v_a_725_, 1);
v_val_716_ = v_val_726_;
goto v___jp_715_;
}
else
{
lean_dec(v_a_725_);
lean_dec(v_fst_710_);
v_a_703_ = v_b_700_;
goto v___jp_702_;
}
}
v___jp_715_:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_700_, v_fst_710_, v_val_716_);
v_a_703_ = v___x_717_;
goto v___jp_702_;
}
}
}
v___jp_702_:
{
size_t v___x_704_; size_t v___x_705_; 
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_699_, v___x_704_);
v_i_699_ = v___x_705_;
v_b_700_ = v_a_703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object* v_as_728_, lean_object* v_sz_729_, lean_object* v_i_730_, lean_object* v_b_731_, lean_object* v___y_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_729_);
lean_dec(v_sz_729_);
v_i_boxed_734_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_728_, v_sz_boxed_733_, v_i_boxed_734_, v_b_731_);
lean_dec_ref(v_as_728_);
return v_res_735_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_box(0);
v___x_737_ = lean_unsigned_to_nat(16u);
v___x_738_ = lean_mk_array(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(size_t v_sz_742_, size_t v_i_743_, lean_object* v_bs_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_743_, v_sz_742_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_bs_744_);
return v___x_749_;
}
else
{
lean_object* v_v_750_; lean_object* v_fst_751_; lean_object* v_snd_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_778_; 
v_v_750_ = lean_array_uget(v_bs_744_, v_i_743_);
v_fst_751_ = lean_ctor_get(v_v_750_, 0);
v_snd_752_ = lean_ctor_get(v_v_750_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_v_750_);
if (v_isSharedCheck_778_ == 0)
{
v___x_754_ = v_v_750_;
v_isShared_755_ = v_isSharedCheck_778_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_snd_752_);
lean_inc(v_fst_751_);
lean_dec(v_v_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_778_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; size_t v_sz_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v_sz_758_ = lean_array_size(v_snd_752_);
v___x_759_ = ((size_t)0ULL);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_snd_752_, v_sz_758_, v___x_759_, v___x_757_);
lean_dec(v_snd_752_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v_bs_x27_762_; lean_object* v___x_764_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v_bs_x27_762_ = lean_array_uset(v_bs_744_, v_i_743_, v___x_756_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_a_761_);
v___x_764_ = v___x_754_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_fst_751_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_761_);
v___x_764_ = v_reuseFailAlloc_769_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_743_, v___x_765_);
v___x_767_ = lean_array_uset(v_bs_x27_762_, v_i_743_, v___x_764_);
v_i_743_ = v___x_766_;
v_bs_744_ = v___x_767_;
goto _start;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_754_);
lean_dec(v_fst_751_);
lean_dec_ref(v_bs_744_);
v_a_770_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_760_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_760_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object* v_sz_779_, lean_object* v_i_780_, lean_object* v_bs_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
size_t v_sz_boxed_785_; size_t v_i_boxed_786_; lean_object* v_res_787_; 
v_sz_boxed_785_ = lean_unbox_usize(v_sz_779_);
lean_dec(v_sz_779_);
v_i_boxed_786_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_sz_boxed_785_, v_i_boxed_786_, v_bs_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object* v_decls_788_, lean_object* v_linters_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; lean_object* v_env_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_793_ = lean_st_ref_get(v_a_791_);
v_env_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_ref(v_env_794_);
lean_dec(v___x_793_);
v_sz_795_ = lean_array_size(v_linters_789_);
v___x_796_ = ((size_t)0ULL);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_env_794_, v_decls_788_, v_sz_795_, v___x_796_, v_linters_789_, v_a_790_, v_a_791_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; size_t v_sz_799_; lean_object* v___x_800_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v_sz_799_ = lean_array_size(v_a_798_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_sz_799_, v___x_796_, v_a_798_, v_a_790_, v_a_791_);
return v___x_800_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_a_801_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_797_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_797_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object* v_decls_809_, lean_object* v_linters_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Linter_EnvLinter_lintCore(v_decls_809_, v_linters_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_decls_809_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_b_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_m_816_, v_a_817_, v_b_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_820_, v_sz_821_, v_i_822_, v_b_823_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object* v_as_828_, lean_object* v_sz_829_, lean_object* v_i_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_sz_boxed_835_ = lean_unbox_usize(v_sz_829_);
lean_dec(v_sz_829_);
v_i_boxed_836_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(v_as_828_, v_sz_boxed_835_, v_i_boxed_836_, v_b_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_as_828_);
return v_res_837_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object* v_00_u03b2_838_, lean_object* v_a_839_, lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_842_, lean_object* v_a_843_, lean_object* v_x_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(v_00_u03b2_842_, v_a_843_, v_x_844_);
lean_dec(v_x_844_);
lean_dec(v_a_843_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object* v_00_u03b2_847_, lean_object* v_data_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_data_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object* v_00_u03b2_850_, lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_851_, v_b_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_855_, lean_object* v_i_856_, lean_object* v_source_857_, lean_object* v_target_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v_i_856_, v_source_857_, v_target_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(v_x_861_, v_x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object* v_a_864_, lean_object* v_fallback_865_, lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_inc(v_fallback_865_);
return v_fallback_865_;
}
else
{
lean_object* v_key_867_; lean_object* v_value_868_; lean_object* v_tail_869_; uint8_t v___x_870_; 
v_key_867_ = lean_ctor_get(v_x_866_, 0);
v_value_868_ = lean_ctor_get(v_x_866_, 1);
v_tail_869_ = lean_ctor_get(v_x_866_, 2);
v___x_870_ = lean_name_eq(v_key_867_, v_a_864_);
if (v___x_870_ == 0)
{
v_x_866_ = v_tail_869_;
goto _start;
}
else
{
lean_inc(v_value_868_);
return v_value_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object* v_a_872_, lean_object* v_fallback_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_872_, v_fallback_873_, v_x_874_);
lean_dec(v_x_874_);
lean_dec(v_fallback_873_);
lean_dec(v_a_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object* v_m_876_, lean_object* v_a_877_, lean_object* v_fallback_878_){
_start:
{
lean_object* v_buckets_879_; lean_object* v___x_880_; uint64_t v___y_882_; 
v_buckets_879_ = lean_ctor_get(v_m_876_, 1);
v___x_880_ = lean_array_get_size(v_buckets_879_);
if (lean_obj_tag(v_a_877_) == 0)
{
uint64_t v___x_896_; 
v___x_896_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_882_ = v___x_896_;
goto v___jp_881_;
}
else
{
uint64_t v_hash_897_; 
v_hash_897_ = lean_ctor_get_uint64(v_a_877_, sizeof(void*)*2);
v___y_882_ = v_hash_897_;
goto v___jp_881_;
}
v___jp_881_:
{
uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v_fold_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_883_ = 32ULL;
v___x_884_ = lean_uint64_shift_right(v___y_882_, v___x_883_);
v_fold_885_ = lean_uint64_xor(v___y_882_, v___x_884_);
v___x_886_ = 16ULL;
v___x_887_ = lean_uint64_shift_right(v_fold_885_, v___x_886_);
v___x_888_ = lean_uint64_xor(v_fold_885_, v___x_887_);
v___x_889_ = lean_uint64_to_usize(v___x_888_);
v___x_890_ = lean_usize_of_nat(v___x_880_);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_sub(v___x_890_, v___x_891_);
v___x_893_ = lean_usize_land(v___x_889_, v___x_892_);
v___x_894_ = lean_array_uget_borrowed(v_buckets_879_, v___x_893_);
v___x_895_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_877_, v_fallback_878_, v___x_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object* v_m_898_, lean_object* v_a_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_898_, v_a_899_, v_fallback_900_);
lean_dec(v_fallback_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_m_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object* v_a_902_, lean_object* v_hi_903_, lean_object* v_pivot_904_, lean_object* v_as_905_, lean_object* v_i_906_, lean_object* v_k_907_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_nat_dec_lt(v_k_907_, v_hi_903_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_k_907_);
v___x_909_ = lean_array_fswap(v_as_905_, v_i_906_, v_hi_903_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_i_906_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v_fst_912_; lean_object* v_fst_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_911_ = lean_array_fget_borrowed(v_as_905_, v_k_907_);
v_fst_912_ = lean_ctor_get(v___x_911_, 0);
v_fst_913_ = lean_ctor_get(v_pivot_904_, 0);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_902_, v_fst_912_, v___x_914_);
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_902_, v_fst_913_, v___x_914_);
v___x_917_ = lean_nat_dec_lt(v___x_915_, v___x_916_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_add(v_k_907_, v___x_918_);
lean_dec(v_k_907_);
v_k_907_ = v___x_919_;
goto _start;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = lean_array_fswap(v_as_905_, v_i_906_, v_k_907_);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_i_906_, v___x_922_);
lean_dec(v_i_906_);
v___x_924_ = lean_nat_add(v_k_907_, v___x_922_);
lean_dec(v_k_907_);
v_as_905_ = v___x_921_;
v_i_906_ = v___x_923_;
v_k_907_ = v___x_924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object* v_a_926_, lean_object* v_hi_927_, lean_object* v_pivot_928_, lean_object* v_as_929_, lean_object* v_i_930_, lean_object* v_k_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_926_, v_hi_927_, v_pivot_928_, v_as_929_, v_i_930_, v_k_931_);
lean_dec_ref(v_pivot_928_);
lean_dec(v_hi_927_);
lean_dec_ref(v_a_926_);
return v_res_932_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object* v_a_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v_fst_936_; lean_object* v_fst_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_fst_936_ = lean_ctor_get(v_x_934_, 0);
v_fst_937_ = lean_ctor_get(v_x_935_, 0);
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_933_, v_fst_936_, v___x_938_);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_933_, v_fst_937_, v___x_938_);
v___x_941_ = lean_nat_dec_lt(v___x_939_, v___x_940_);
lean_dec(v___x_940_);
lean_dec(v___x_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object* v_a_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_942_, v_x_943_, v_x_944_);
lean_dec_ref(v_x_944_);
lean_dec_ref(v_x_943_);
lean_dec_ref(v_a_942_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object* v_a_947_, lean_object* v_n_948_, lean_object* v_as_949_, lean_object* v_lo_950_, lean_object* v_hi_951_){
_start:
{
lean_object* v___y_953_; uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_lt(v_lo_950_, v_hi_951_);
if (v___x_963_ == 0)
{
lean_dec(v_lo_950_);
return v_as_949_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_mid_966_; lean_object* v___y_968_; lean_object* v___y_974_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_964_ = lean_nat_add(v_lo_950_, v_hi_951_);
v___x_965_ = lean_unsigned_to_nat(1u);
v_mid_966_ = lean_nat_shiftr(v___x_964_, v___x_965_);
lean_dec(v___x_964_);
v___x_979_ = lean_array_fget_borrowed(v_as_949_, v_mid_966_);
v___x_980_ = lean_array_fget_borrowed(v_as_949_, v_lo_950_);
v___x_981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_947_, v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
v___y_974_ = v_as_949_;
goto v___jp_973_;
}
else
{
lean_object* v___x_982_; 
v___x_982_ = lean_array_fswap(v_as_949_, v_lo_950_, v_mid_966_);
v___y_974_ = v___x_982_;
goto v___jp_973_;
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = lean_array_fget_borrowed(v___y_968_, v_mid_966_);
v___x_970_ = lean_array_fget_borrowed(v___y_968_, v_hi_951_);
v___x_971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_947_, v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_mid_966_);
v___y_953_ = v___y_968_;
goto v___jp_952_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_array_fswap(v___y_968_, v_mid_966_, v_hi_951_);
lean_dec(v_mid_966_);
v___y_953_ = v___x_972_;
goto v___jp_952_;
}
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_array_fget_borrowed(v___y_974_, v_hi_951_);
v___x_976_ = lean_array_fget_borrowed(v___y_974_, v_lo_950_);
v___x_977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_947_, v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
v___y_968_ = v___y_974_;
goto v___jp_967_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_array_fswap(v___y_974_, v_lo_950_, v_hi_951_);
v___y_968_ = v___x_978_;
goto v___jp_967_;
}
}
}
v___jp_952_:
{
lean_object* v_pivot_954_; lean_object* v___x_955_; lean_object* v_fst_956_; lean_object* v_snd_957_; uint8_t v___x_958_; 
v_pivot_954_ = lean_array_fget(v___y_953_, v_hi_951_);
lean_inc_n(v_lo_950_, 2);
v___x_955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_947_, v_hi_951_, v_pivot_954_, v___y_953_, v_lo_950_, v_lo_950_);
lean_dec(v_pivot_954_);
v_fst_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_fst_956_);
v_snd_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_snd_957_);
lean_dec_ref(v___x_955_);
v___x_958_ = lean_nat_dec_le(v_hi_951_, v_fst_956_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_947_, v_n_948_, v_snd_957_, v_lo_950_, v_fst_956_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_fst_956_, v___x_960_);
lean_dec(v_fst_956_);
v_as_949_ = v___x_959_;
v_lo_950_ = v___x_961_;
goto _start;
}
else
{
lean_dec(v_fst_956_);
lean_dec(v_lo_950_);
return v_snd_957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object* v_a_983_, lean_object* v_n_984_, lean_object* v_as_985_, lean_object* v_lo_986_, lean_object* v_hi_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_983_, v_n_984_, v_as_985_, v_lo_986_, v_hi_987_);
lean_dec(v_hi_987_);
lean_dec(v_n_984_);
lean_dec_ref(v_a_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object* v_declName_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; lean_object* v_env_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_992_ = lean_st_ref_get(v___y_990_);
v_env_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc_ref(v_env_993_);
lean_dec(v___x_992_);
v___x_994_ = l_Lean_isRecCore(v_env_993_, v_declName_989_);
v___x_995_ = lean_box(v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object* v_declName_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_997_, v___y_998_);
lean_dec(v___y_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object* v_declName_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_env_1005_; lean_object* v___x_1006_; lean_object* v_env_1007_; lean_object* v___x_1008_; lean_object* v_toEnvExtension_1009_; lean_object* v_asyncMode_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1004_ = lean_st_ref_get(v___y_1002_);
v_env_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc_ref(v_env_1005_);
lean_dec(v___x_1004_);
v___x_1006_ = lean_st_ref_get(v___y_1002_);
v_env_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc_ref(v_env_1007_);
lean_dec(v___x_1006_);
v___x_1008_ = l_Lean_declRangeExt;
v_toEnvExtension_1009_ = lean_ctor_get(v___x_1008_, 0);
v_asyncMode_1010_ = lean_ctor_get(v_toEnvExtension_1009_, 2);
v___x_1011_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1012_ = 0;
lean_inc(v_declName_1001_);
v___x_1013_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1011_, v___x_1008_, v_env_1005_, v_declName_1001_, v_asyncMode_1010_, v___x_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = 1;
v___x_1015_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1011_, v___x_1008_, v_env_1007_, v_declName_1001_, v_asyncMode_1010_, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; 
lean_dec_ref(v_env_1007_);
lean_dec(v_declName_1001_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1013_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1018_, v___y_1019_);
lean_dec(v___y_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object* v_declName_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_ranges_1027_; lean_object* v___x_1033_; lean_object* v_env_1034_; lean_object* v___x_1035_; lean_object* v_a_1036_; uint8_t v___y_1042_; uint8_t v___x_1046_; 
v___x_1033_ = lean_st_ref_get(v___y_1024_);
v_env_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref_n(v_env_1034_, 2);
lean_dec(v___x_1033_);
lean_inc_n(v_declName_1022_, 2);
v___x_1035_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1022_, v___y_1024_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___x_1046_ = l_Lean_isAuxRecursor(v_env_1034_, v_declName_1022_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; 
lean_inc(v_declName_1022_);
v___x_1047_ = l_Lean_isNoConfusion(v_env_1034_, v_declName_1022_);
v___y_1042_ = v___x_1047_;
goto v___jp_1041_;
}
else
{
lean_dec_ref(v_env_1034_);
v___y_1042_ = v___x_1046_;
goto v___jp_1041_;
}
v___jp_1026_:
{
if (lean_obj_tag(v_ranges_1027_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = l_Lean_builtinDeclRanges;
v___x_1029_ = lean_st_ref_get(v___x_1028_);
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1029_, v_declName_1022_);
lean_dec(v_declName_1022_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_declName_1022_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_ranges_1027_);
return v___x_1032_;
}
}
v___jp_1037_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; 
v___x_1038_ = l_Lean_Name_getPrefix(v_declName_1022_);
v___x_1039_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v___x_1038_, v___y_1024_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v_ranges_1027_ = v_a_1040_;
goto v___jp_1026_;
}
v___jp_1041_:
{
if (v___y_1042_ == 0)
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_unbox(v_a_1036_);
lean_dec(v_a_1036_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_a_1045_; 
lean_inc(v_declName_1022_);
v___x_1044_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1022_, v___y_1024_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
v_ranges_1027_ = v_a_1045_;
goto v___jp_1026_;
}
else
{
goto v___jp_1037_;
}
}
else
{
lean_dec(v_a_1036_);
goto v___jp_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object* v_declName_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object* v_as_1053_, size_t v_sz_1054_, size_t v_i_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_usize_dec_lt(v_i_1055_, v_sz_1054_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_b_1056_);
return v___x_1061_;
}
else
{
lean_object* v_a_1062_; lean_object* v_fst_1063_; lean_object* v___x_1064_; 
v_a_1062_ = lean_array_uget_borrowed(v_as_1053_, v_i_1055_);
v_fst_1063_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_fst_1063_);
v___x_1064_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_fst_1063_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_a_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
if (lean_obj_tag(v_a_1065_) == 1)
{
lean_object* v_val_1071_; lean_object* v_range_1072_; lean_object* v_pos_1073_; lean_object* v_line_1074_; lean_object* v___x_1075_; 
v_val_1071_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v_a_1065_, 1);
v_range_1072_ = lean_ctor_get(v_val_1071_, 0);
lean_inc_ref(v_range_1072_);
lean_dec(v_val_1071_);
v_pos_1073_ = lean_ctor_get(v_range_1072_, 0);
lean_inc_ref(v_pos_1073_);
lean_dec_ref(v_range_1072_);
v_line_1074_ = lean_ctor_get(v_pos_1073_, 0);
lean_inc(v_line_1074_);
lean_dec_ref(v_pos_1073_);
lean_inc(v_fst_1063_);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_1056_, v_fst_1063_, v_line_1074_);
v_a_1067_ = v___x_1075_;
goto v___jp_1066_;
}
else
{
lean_dec(v_a_1065_);
v_a_1067_ = v_b_1056_;
goto v___jp_1066_;
}
v___jp_1066_:
{
size_t v___x_1068_; size_t v___x_1069_; 
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1055_, v___x_1068_);
v_i_1055_ = v___x_1069_;
v_b_1056_ = v_a_1067_;
goto _start;
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_b_1056_);
v_a_1076_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1064_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1064_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object* v_as_1084_, lean_object* v_sz_1085_, lean_object* v_i_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
size_t v_sz_boxed_1091_; size_t v_i_boxed_1092_; lean_object* v_res_1093_; 
v_sz_boxed_1091_ = lean_unbox_usize(v_sz_1085_);
lean_dec(v_sz_1085_);
v_i_boxed_1092_ = lean_unbox_usize(v_i_1086_);
lean_dec(v_i_1086_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1084_, v_sz_boxed_1091_, v_i_boxed_1092_, v_b_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec_ref(v_as_1084_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
if (lean_obj_tag(v_x_1095_) == 0)
{
return v_x_1094_;
}
else
{
lean_object* v_key_1096_; lean_object* v_value_1097_; lean_object* v_tail_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_key_1096_ = lean_ctor_get(v_x_1095_, 0);
v_value_1097_ = lean_ctor_get(v_x_1095_, 1);
v_tail_1098_ = lean_ctor_get(v_x_1095_, 2);
lean_inc(v_value_1097_);
lean_inc(v_key_1096_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_key_1096_);
lean_ctor_set(v___x_1099_, 1, v_value_1097_);
v___x_1100_ = lean_array_push(v_x_1094_, v___x_1099_);
v_x_1094_ = v___x_1100_;
v_x_1095_ = v_tail_1098_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1102_, v_x_1103_);
lean_dec(v_x_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object* v_as_1105_, size_t v_i_1106_, size_t v_stop_1107_, lean_object* v_b_1108_){
_start:
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_usize_dec_eq(v_i_1106_, v_stop_1107_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; 
v___x_1110_ = lean_array_uget_borrowed(v_as_1105_, v_i_1106_);
v___x_1111_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_b_1108_, v___x_1110_);
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_add(v_i_1106_, v___x_1112_);
v_i_1106_ = v___x_1113_;
v_b_1108_ = v___x_1111_;
goto _start;
}
else
{
return v_b_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object* v_as_1115_, lean_object* v_i_1116_, lean_object* v_stop_1117_, lean_object* v_b_1118_){
_start:
{
size_t v_i_boxed_1119_; size_t v_stop_boxed_1120_; lean_object* v_res_1121_; 
v_i_boxed_1119_ = lean_unbox_usize(v_i_1116_);
lean_dec(v_i_1116_);
v_stop_boxed_1120_ = lean_unbox_usize(v_stop_1117_);
lean_dec(v_stop_1117_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1115_, v_i_boxed_1119_, v_stop_boxed_1120_, v_b_1118_);
lean_dec_ref(v_as_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object* v_results_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v_size_1141_; lean_object* v_buckets_1142_; lean_object* v___x_1143_; lean_object* v_key_1144_; lean_object* v___y_1146_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_size_1141_ = lean_ctor_get(v_results_1122_, 0);
v_buckets_1142_ = lean_ctor_get(v_results_1122_, 1);
v___x_1143_ = lean_unsigned_to_nat(0u);
v_key_1144_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v___x_1171_ = lean_mk_empty_array_with_capacity(v_size_1141_);
v___x_1172_ = lean_array_get_size(v_buckets_1142_);
v___x_1173_ = lean_nat_dec_lt(v___x_1143_, v___x_1172_);
if (v___x_1173_ == 0)
{
v___y_1146_ = v___x_1171_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_le(v___x_1172_, v___x_1172_);
if (v___x_1174_ == 0)
{
if (v___x_1173_ == 0)
{
v___y_1146_ = v___x_1171_;
goto v___jp_1145_;
}
else
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = lean_usize_of_nat(v___x_1172_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1142_, v___x_1175_, v___x_1176_, v___x_1171_);
v___y_1146_ = v___x_1177_;
goto v___jp_1145_;
}
}
else
{
size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = ((size_t)0ULL);
v___x_1179_ = lean_usize_of_nat(v___x_1172_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1142_, v___x_1178_, v___x_1179_, v___x_1171_);
v___y_1146_ = v___x_1180_;
goto v___jp_1145_;
}
}
v___jp_1126_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v___y_1129_, v___y_1130_, v___y_1127_, v___y_1128_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
v___jp_1134_:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_le(v___y_1139_, v___y_1136_);
if (v___x_1140_ == 0)
{
lean_dec(v___y_1136_);
lean_inc(v___y_1139_);
v___y_1127_ = v___y_1135_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1137_;
v___y_1130_ = v___y_1138_;
v___y_1131_ = v___y_1139_;
goto v___jp_1126_;
}
else
{
v___y_1127_ = v___y_1135_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1137_;
v___y_1130_ = v___y_1138_;
v___y_1131_ = v___y_1136_;
goto v___jp_1126_;
}
}
v___jp_1145_:
{
size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v_sz_1147_ = lean_array_size(v___y_1146_);
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v___y_1146_, v_sz_1147_, v___x_1148_, v_key_1144_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1162_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_array_get_size(v___y_1146_);
v___x_1155_ = lean_nat_dec_eq(v___x_1154_, v___x_1143_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
lean_del_object(v___x_1152_);
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_sub(v___x_1154_, v___x_1156_);
v___x_1158_ = lean_nat_dec_le(v___x_1143_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_inc(v___x_1157_);
v___y_1135_ = v___y_1146_;
v___y_1136_ = v___x_1157_;
v___y_1137_ = v_a_1150_;
v___y_1138_ = v___x_1154_;
v___y_1139_ = v___x_1157_;
goto v___jp_1134_;
}
else
{
v___y_1135_ = v___y_1146_;
v___y_1136_ = v___x_1157_;
v___y_1137_ = v_a_1150_;
v___y_1138_ = v___x_1154_;
v___y_1139_ = v___x_1143_;
goto v___jp_1134_;
}
}
else
{
lean_object* v___x_1160_; 
lean_dec(v_a_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___y_1146_);
v___x_1160_ = v___x_1152_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___y_1146_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___y_1146_);
v_a_1163_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1149_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1149_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object* v_results_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec_ref(v_results_1181_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object* v_00_u03b1_1186_, lean_object* v_results_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1187_, v_a_1188_, v_a_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_results_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Linter_EnvLinter_sortResults(v_00_u03b1_1192_, v_results_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec_ref(v_results_1193_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object* v_declName_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1198_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object* v_declName_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(v_declName_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object* v_declName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1208_, v___y_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object* v_declName_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(v_declName_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object* v_00_u03b1_1218_, lean_object* v_as_1219_, size_t v_sz_1220_, size_t v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1219_, v_sz_1220_, v_i_1221_, v_b_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(v_00_u03b1_1227_, v_as_1228_, v_sz_boxed_1235_, v_i_boxed_1236_, v_b_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec_ref(v_as_1228_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object* v_00_u03b2_1238_, lean_object* v_m_1239_, lean_object* v_a_1240_, lean_object* v_fallback_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1239_, v_a_1240_, v_fallback_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_, lean_object* v_fallback_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(v_00_u03b2_1243_, v_m_1244_, v_a_1245_, v_fallback_1246_);
lean_dec(v_fallback_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_m_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object* v_00_u03b1_1248_, lean_object* v_a_1249_, lean_object* v_n_1250_, lean_object* v_as_1251_, lean_object* v_lo_1252_, lean_object* v_hi_1253_, lean_object* v_w_1254_, lean_object* v_hlo_1255_, lean_object* v_hhi_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1249_, v_n_1250_, v_as_1251_, v_lo_1252_, v_hi_1253_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_a_1259_, lean_object* v_n_1260_, lean_object* v_as_1261_, lean_object* v_lo_1262_, lean_object* v_hi_1263_, lean_object* v_w_1264_, lean_object* v_hlo_1265_, lean_object* v_hhi_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(v_00_u03b1_1258_, v_a_1259_, v_n_1260_, v_as_1261_, v_lo_1262_, v_hi_1263_, v_w_1264_, v_hlo_1265_, v_hhi_1266_);
lean_dec(v_hi_1263_);
lean_dec(v_n_1260_);
lean_dec_ref(v_a_1259_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object* v_00_u03b1_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1269_, v_x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(v_00_u03b1_1272_, v_x_1273_, v_x_1274_);
lean_dec(v_x_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object* v_00_u03b1_1276_, lean_object* v_as_1277_, size_t v_i_1278_, size_t v_stop_1279_, lean_object* v_b_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1277_, v_i_1278_, v_stop_1279_, v_b_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_as_1283_, lean_object* v_i_1284_, lean_object* v_stop_1285_, lean_object* v_b_1286_){
_start:
{
size_t v_i_boxed_1287_; size_t v_stop_boxed_1288_; lean_object* v_res_1289_; 
v_i_boxed_1287_ = lean_unbox_usize(v_i_1284_);
lean_dec(v_i_1284_);
v_stop_boxed_1288_ = lean_unbox_usize(v_stop_1285_);
lean_dec(v_stop_1285_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(v_00_u03b1_1282_, v_as_1283_, v_i_boxed_1287_, v_stop_boxed_1288_, v_b_1286_);
lean_dec_ref(v_as_1283_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_fallback_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1291_, v_fallback_1292_, v_x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_a_1296_, lean_object* v_fallback_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(v_00_u03b2_1295_, v_a_1296_, v_fallback_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec(v_fallback_1297_);
lean_dec(v_a_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object* v_00_u03b1_1300_, lean_object* v_a_1301_, lean_object* v_n_1302_, lean_object* v_lo_1303_, lean_object* v_hi_1304_, lean_object* v_hhi_1305_, lean_object* v_pivot_1306_, lean_object* v_as_1307_, lean_object* v_i_1308_, lean_object* v_k_1309_, lean_object* v_ilo_1310_, lean_object* v_ik_1311_, lean_object* v_w_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1301_, v_hi_1304_, v_pivot_1306_, v_as_1307_, v_i_1308_, v_k_1309_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_a_1315_, lean_object* v_n_1316_, lean_object* v_lo_1317_, lean_object* v_hi_1318_, lean_object* v_hhi_1319_, lean_object* v_pivot_1320_, lean_object* v_as_1321_, lean_object* v_i_1322_, lean_object* v_k_1323_, lean_object* v_ilo_1324_, lean_object* v_ik_1325_, lean_object* v_w_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(v_00_u03b1_1314_, v_a_1315_, v_n_1316_, v_lo_1317_, v_hi_1318_, v_hhi_1319_, v_pivot_1320_, v_as_1321_, v_i_1322_, v_k_1323_, v_ilo_1324_, v_ik_1325_, v_w_1326_);
lean_dec_ref(v_pivot_1320_);
lean_dec(v_hi_1318_);
lean_dec(v_lo_1317_);
lean_dec(v_n_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1327_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
lean_ctor_set(v___x_1330_, 3, v___x_1329_);
lean_ctor_set(v___x_1330_, 4, v___x_1328_);
lean_ctor_set(v___x_1330_, 5, v___x_1328_);
lean_ctor_set(v___x_1330_, 6, v___x_1328_);
lean_ctor_set(v___x_1330_, 7, v___x_1328_);
lean_ctor_set(v___x_1330_, 8, v___x_1328_);
lean_ctor_set(v___x_1330_, 9, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_unsigned_to_nat(32u);
v___x_1332_ = lean_mk_empty_array_with_capacity(v___x_1331_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2(void){
_start:
{
size_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1334_ = ((size_t)5ULL);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_unsigned_to_nat(32u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1);
v___x_1339_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
lean_ctor_set(v___x_1339_, 2, v___x_1335_);
lean_ctor_set(v___x_1339_, 3, v___x_1335_);
lean_ctor_set_usize(v___x_1339_, 4, v___x_1334_);
return v___x_1339_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_box(1);
v___x_1341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2);
v___x_1342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
lean_ctor_set(v___x_1343_, 2, v___x_1340_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object* v_msgData_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v_env_1349_; lean_object* v_options_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1348_ = lean_st_ref_get(v___y_1346_);
v_env_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_ref(v_env_1349_);
lean_dec(v___x_1348_);
v_options_1350_ = lean_ctor_get(v___y_1345_, 2);
v___x_1351_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
lean_inc_ref(v_options_1350_);
v___x_1353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1353_, 0, v_env_1349_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
lean_ctor_set(v___x_1353_, 3, v_options_1350_);
v___x_1354_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v_msgData_1344_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object* v_msgData_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msgData_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
if (lean_obj_tag(v_a_1361_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = l_List_reverse___redArg(v_a_1362_);
return v___x_1363_;
}
else
{
lean_object* v_head_1364_; lean_object* v_tail_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1374_; 
v_head_1364_ = lean_ctor_get(v_a_1361_, 0);
v_tail_1365_ = lean_ctor_get(v_a_1361_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_a_1361_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1367_ = v_a_1361_;
v_isShared_1368_ = v_isSharedCheck_1374_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_tail_1365_);
lean_inc(v_head_1364_);
lean_dec(v_a_1361_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1374_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = l_Lean_mkLevelParam(v_head_1364_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v_a_1362_);
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1362_);
v___x_1371_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
v_a_1361_ = v_tail_1365_;
v_a_1362_ = v___x_1371_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_ref_1379_; lean_object* v___x_1380_; lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1389_; 
v_ref_1379_ = lean_ctor_get(v___y_1376_, 5);
v___x_1380_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msg_1375_, v___y_1376_, v___y_1377_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1389_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1389_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_inc(v_ref_1379_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_ref_1379_);
lean_ctor_set(v___x_1385_, 1, v_a_1381_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 1);
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_1395_, lean_object* v_msg_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_fileName_1400_; lean_object* v_fileMap_1401_; lean_object* v_options_1402_; lean_object* v_currRecDepth_1403_; lean_object* v_maxRecDepth_1404_; lean_object* v_ref_1405_; lean_object* v_currNamespace_1406_; lean_object* v_openDecls_1407_; lean_object* v_initHeartbeats_1408_; lean_object* v_maxHeartbeats_1409_; lean_object* v_quotContext_1410_; lean_object* v_currMacroScope_1411_; uint8_t v_diag_1412_; lean_object* v_cancelTk_x3f_1413_; uint8_t v_suppressElabErrors_1414_; lean_object* v_inheritedTraceOptions_1415_; lean_object* v_ref_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_fileName_1400_ = lean_ctor_get(v___y_1397_, 0);
v_fileMap_1401_ = lean_ctor_get(v___y_1397_, 1);
v_options_1402_ = lean_ctor_get(v___y_1397_, 2);
v_currRecDepth_1403_ = lean_ctor_get(v___y_1397_, 3);
v_maxRecDepth_1404_ = lean_ctor_get(v___y_1397_, 4);
v_ref_1405_ = lean_ctor_get(v___y_1397_, 5);
v_currNamespace_1406_ = lean_ctor_get(v___y_1397_, 6);
v_openDecls_1407_ = lean_ctor_get(v___y_1397_, 7);
v_initHeartbeats_1408_ = lean_ctor_get(v___y_1397_, 8);
v_maxHeartbeats_1409_ = lean_ctor_get(v___y_1397_, 9);
v_quotContext_1410_ = lean_ctor_get(v___y_1397_, 10);
v_currMacroScope_1411_ = lean_ctor_get(v___y_1397_, 11);
v_diag_1412_ = lean_ctor_get_uint8(v___y_1397_, sizeof(void*)*14);
v_cancelTk_x3f_1413_ = lean_ctor_get(v___y_1397_, 12);
v_suppressElabErrors_1414_ = lean_ctor_get_uint8(v___y_1397_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1415_ = lean_ctor_get(v___y_1397_, 13);
v_ref_1416_ = l_Lean_replaceRef(v_ref_1395_, v_ref_1405_);
lean_inc_ref(v_inheritedTraceOptions_1415_);
lean_inc(v_cancelTk_x3f_1413_);
lean_inc(v_currMacroScope_1411_);
lean_inc(v_quotContext_1410_);
lean_inc(v_maxHeartbeats_1409_);
lean_inc(v_initHeartbeats_1408_);
lean_inc(v_openDecls_1407_);
lean_inc(v_currNamespace_1406_);
lean_inc(v_maxRecDepth_1404_);
lean_inc(v_currRecDepth_1403_);
lean_inc_ref(v_options_1402_);
lean_inc_ref(v_fileMap_1401_);
lean_inc_ref(v_fileName_1400_);
v___x_1417_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1417_, 0, v_fileName_1400_);
lean_ctor_set(v___x_1417_, 1, v_fileMap_1401_);
lean_ctor_set(v___x_1417_, 2, v_options_1402_);
lean_ctor_set(v___x_1417_, 3, v_currRecDepth_1403_);
lean_ctor_set(v___x_1417_, 4, v_maxRecDepth_1404_);
lean_ctor_set(v___x_1417_, 5, v_ref_1416_);
lean_ctor_set(v___x_1417_, 6, v_currNamespace_1406_);
lean_ctor_set(v___x_1417_, 7, v_openDecls_1407_);
lean_ctor_set(v___x_1417_, 8, v_initHeartbeats_1408_);
lean_ctor_set(v___x_1417_, 9, v_maxHeartbeats_1409_);
lean_ctor_set(v___x_1417_, 10, v_quotContext_1410_);
lean_ctor_set(v___x_1417_, 11, v_currMacroScope_1411_);
lean_ctor_set(v___x_1417_, 12, v_cancelTk_x3f_1413_);
lean_ctor_set(v___x_1417_, 13, v_inheritedTraceOptions_1415_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*14, v_diag_1412_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*14 + 1, v_suppressElabErrors_1414_);
v___x_1418_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1396_, v___x_1417_, v___y_1398_);
lean_dec_ref_known(v___x_1417_, 14);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1419_, lean_object* v_msg_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1419_, v_msg_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v_ref_1419_);
return v_res_1424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_1427_ = l_Lean_stringToMessageData(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_1430_ = l_Lean_stringToMessageData(v___x_1429_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_1433_ = l_Lean_stringToMessageData(v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1436_ = l_Lean_stringToMessageData(v___x_1435_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1439_ = l_Lean_stringToMessageData(v___x_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1442_ = l_Lean_stringToMessageData(v___x_1441_);
return v___x_1442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1446_, lean_object* v_declHint_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v_env_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_st_ref_get(v___y_1448_);
v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_Name_isAnonymous(v_declHint_1447_);
if (v___x_1452_ == 0)
{
uint8_t v_isExporting_1453_; 
v_isExporting_1453_ = lean_ctor_get_uint8(v_env_1451_, sizeof(void*)*8);
if (v_isExporting_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref(v_env_1451_);
lean_dec(v_declHint_1447_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_msg_1446_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
lean_inc_ref(v_env_1451_);
v___x_1455_ = l_Lean_Environment_setExporting(v_env_1451_, v___x_1452_);
lean_inc(v_declHint_1447_);
lean_inc_ref(v___x_1455_);
v___x_1456_ = l_Lean_Environment_contains(v___x_1455_, v_declHint_1447_, v_isExporting_1453_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec_ref(v___x_1455_);
lean_dec_ref(v_env_1451_);
lean_dec(v_declHint_1447_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_msg_1446_);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_c_1463_; lean_object* v___x_1464_; 
v___x_1458_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1459_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
v___x_1460_ = l_Lean_Options_empty;
v___x_1461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1455_);
lean_ctor_set(v___x_1461_, 1, v___x_1458_);
lean_ctor_set(v___x_1461_, 2, v___x_1459_);
lean_ctor_set(v___x_1461_, 3, v___x_1460_);
lean_inc(v_declHint_1447_);
v___x_1462_ = l_Lean_MessageData_ofConstName(v_declHint_1447_, v___x_1452_);
v_c_1463_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1463_, 0, v___x_1461_);
lean_ctor_set(v_c_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1451_, v_declHint_1447_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_env_1451_);
lean_dec(v_declHint_1447_);
v___x_1465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v_c_1463_);
v___x_1467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_MessageData_note(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_msg_1446_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
else
{
lean_object* v_val_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1507_; 
v_val_1472_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1474_ = v___x_1464_;
v_isShared_1475_ = v_isSharedCheck_1507_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_val_1472_);
lean_dec(v___x_1464_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1507_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_mod_1479_; uint8_t v___x_1480_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Lean_Environment_header(v_env_1451_);
lean_dec_ref(v_env_1451_);
v___x_1478_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1477_);
v_mod_1479_ = lean_array_get(v___x_1476_, v___x_1478_, v_val_1472_);
lean_dec(v_val_1472_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = l_Lean_isPrivateName(v_declHint_1447_);
lean_dec(v_declHint_1447_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_c_1463_);
v___x_1483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_MessageData_ofName(v_mod_1479_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_MessageData_note(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_msg_1446_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1490_);
v___x_1492_ = v___x_1474_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1494_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_c_1463_);
v___x_1496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_MessageData_ofName(v_mod_1479_);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = l_Lean_MessageData_note(v___x_1501_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_msg_1446_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1503_);
v___x_1505_ = v___x_1474_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1508_; 
lean_dec_ref(v_env_1451_);
lean_dec(v_declHint_1447_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_msg_1446_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1509_, lean_object* v_declHint_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1509_, v_declHint_1510_, v___y_1511_);
lean_dec(v___y_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1529_; 
v___x_1519_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1514_, v_declHint_1515_, v___y_1517_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1524_ = l_Lean_unknownIdentifierMessageTag;
v___x_1525_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_1530_, lean_object* v_declHint_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1530_, v_declHint_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1536_, lean_object* v_msg_1537_, lean_object* v_declHint_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v_a_1543_; lean_object* v___x_1544_; 
v___x_1542_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1537_, v_declHint_1538_, v___y_1539_, v___y_1540_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1536_, v_a_1543_, v___y_1539_, v___y_1540_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1545_, lean_object* v_msg_1546_, lean_object* v_declHint_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1545_, v_msg_1546_, v_declHint_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v_ref_1545_);
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1558_, lean_object* v_constName_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1563_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1564_ = 0;
lean_inc(v_constName_1559_);
v___x_1565_ = l_Lean_MessageData_ofConstName(v_constName_1559_, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1563_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1558_, v___x_1568_, v_constName_1559_, v___y_1560_, v___y_1561_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1570_, lean_object* v_constName_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1570_, v_constName_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_ref_1570_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_ref_1580_; lean_object* v___x_1581_; 
v_ref_1580_ = lean_ctor_get(v___y_1577_, 5);
v___x_1581_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1580_, v_constName_1576_, v___y_1577_, v___y_1578_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object* v_constName_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v_env_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = lean_st_ref_get(v___y_1589_);
v_env_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc_ref(v_env_1592_);
lean_dec(v___x_1591_);
v___x_1593_ = 0;
lean_inc(v_constName_1587_);
v___x_1594_ = l_Lean_Environment_findConstVal_x3f(v_env_1592_, v_constName_1587_, v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1587_, v___y_1588_, v___y_1589_);
return v___x_1595_;
}
else
{
lean_object* v_val_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_constName_1587_);
v_val_1596_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1594_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_val_1596_);
lean_dec(v___x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 0);
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_val_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object* v_constName_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object* v_constName_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
lean_inc(v_constName_1609_);
v___x_1613_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1625_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v_levelParams_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v_levelParams_1618_ = lean_ctor_get(v_a_1614_, 1);
lean_inc(v_levelParams_1618_);
lean_dec(v_a_1614_);
v___x_1619_ = lean_box(0);
v___x_1620_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(v_levelParams_1618_, v___x_1619_);
v___x_1621_ = l_Lean_mkConst(v_constName_1609_, v___x_1620_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1621_);
v___x_1623_ = v___x_1616_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_constName_1609_);
v_a_1626_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1613_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1613_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object* v_constName_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_constName_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1638_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__1(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__0));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__3(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__2));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__5(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__4));
v___x_1647_ = l_Lean_stringToMessageData(v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__7(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__6));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__9(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__8));
v___x_1653_ = l_Lean_stringToMessageData(v___x_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__11(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__10));
v___x_1656_ = l_Lean_stringToMessageData(v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object* v_declName_1657_, lean_object* v_warning_1658_, uint8_t v_useErrorFormat_1659_, lean_object* v_filePath_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___y_1665_; lean_object* v___y_1666_; 
if (v_useErrorFormat_1659_ == 0)
{
lean_dec_ref(v_filePath_1660_);
v___y_1665_ = v_a_1661_;
v___y_1666_ = v_a_1662_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1686_; 
lean_inc(v_declName_1657_);
v___x_1686_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1657_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
if (lean_obj_tag(v_a_1687_) == 1)
{
lean_object* v_val_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1744_; 
v_val_1688_ = lean_ctor_get(v_a_1687_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1687_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1690_ = v_a_1687_;
v_isShared_1691_ = v_isSharedCheck_1744_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_val_1688_);
lean_dec(v_a_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1744_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1657_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_range_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1734_; 
v_range_1693_ = lean_ctor_get(v_val_1688_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_val_1688_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_val_1688_, 1);
lean_dec(v_unused_1735_);
v___x_1695_ = v_val_1688_;
v_isShared_1696_ = v_isSharedCheck_1734_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_range_1693_);
lean_dec(v_val_1688_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1734_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_pos_1697_; lean_object* v_a_1698_; lean_object* v_line_1699_; lean_object* v_column_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1733_; 
v_pos_1697_ = lean_ctor_get(v_range_1693_, 0);
lean_inc_ref(v_pos_1697_);
lean_dec_ref(v_range_1693_);
v_a_1698_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1692_, 1);
v_line_1699_ = lean_ctor_get(v_pos_1697_, 0);
v_column_1700_ = lean_ctor_get(v_pos_1697_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_pos_1697_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1702_ = v_pos_1697_;
v_isShared_1703_ = v_isSharedCheck_1733_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_column_1700_);
lean_inc(v_line_1699_);
lean_dec(v_pos_1697_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1733_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 3);
lean_ctor_set(v___x_1690_, 0, v_filePath_1660_);
v___x_1705_ = v___x_1690_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_filePath_1660_);
v___x_1705_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1706_ = l_Lean_MessageData_ofFormat(v___x_1705_);
v___x_1707_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__7, &l_Lean_Linter_EnvLinter_printWarning___closed__7_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__7);
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 7);
lean_ctor_set(v___x_1702_, 1, v___x_1707_);
lean_ctor_set(v___x_1702_, 0, v___x_1706_);
v___x_1709_ = v___x_1702_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1710_ = l_Nat_reprFast(v_line_1699_);
v___x_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
v___x_1712_ = l_Lean_MessageData_ofFormat(v___x_1711_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 7);
lean_ctor_set(v___x_1695_, 1, v___x_1712_);
lean_ctor_set(v___x_1695_, 0, v___x_1709_);
v___x_1714_ = v___x_1695_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___x_1707_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_column_1700_, v___x_1716_);
lean_dec(v_column_1700_);
v___x_1718_ = l_Nat_reprFast(v___x_1717_);
v___x_1719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
v___x_1720_ = l_Lean_MessageData_ofFormat(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1715_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__9, &l_Lean_Linter_EnvLinter_printWarning___closed__9_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__9);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = l_Lean_MessageData_ofExpr(v_a_1698_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__11, &l_Lean_Linter_EnvLinter_printWarning___closed__11_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__11);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
lean_ctor_set(v___x_1728_, 1, v_warning_1658_);
v___x_1729_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1728_, v_a_1661_, v_a_1662_);
return v___x_1729_;
}
}
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_del_object(v___x_1690_);
lean_dec(v_val_1688_);
lean_dec_ref(v_filePath_1660_);
lean_dec_ref(v_warning_1658_);
v_a_1736_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1692_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1692_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_dec(v_a_1687_);
lean_dec_ref(v_filePath_1660_);
v___y_1665_ = v_a_1661_;
v___y_1666_ = v_a_1662_;
goto v___jp_1664_;
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_filePath_1660_);
lean_dec_ref(v_warning_1658_);
lean_dec(v_declName_1657_);
v_a_1745_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1686_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1686_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
v___jp_1664_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1657_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__1, &l_Lean_Linter_EnvLinter_printWarning___closed__1_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__1);
v___x_1670_ = l_Lean_MessageData_ofExpr(v_a_1668_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__3, &l_Lean_Linter_EnvLinter_printWarning___closed__3_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__3);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_warning_1658_);
v___x_1675_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1676_, v___y_1665_, v___y_1666_);
return v___x_1677_;
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v_warning_1658_);
v_a_1678_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1667_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1667_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object* v_declName_1753_, lean_object* v_warning_1754_, lean_object* v_useErrorFormat_1755_, lean_object* v_filePath_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
uint8_t v_useErrorFormat_boxed_1760_; lean_object* v_res_1761_; 
v_useErrorFormat_boxed_1760_ = lean_unbox(v_useErrorFormat_1755_);
v_res_1761_ = l_Lean_Linter_EnvLinter_printWarning(v_declName_1753_, v_warning_1754_, v_useErrorFormat_boxed_1760_, v_filePath_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1762_, lean_object* v_constName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_constName_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(v_00_u03b1_1768_, v_constName_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1774_, lean_object* v_ref_1775_, lean_object* v_constName_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1775_, v_constName_1776_, v___y_1777_, v___y_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_ref_1782_, lean_object* v_constName_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1781_, v_ref_1782_, v_constName_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v_ref_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1788_, lean_object* v_ref_1789_, lean_object* v_msg_1790_, lean_object* v_declHint_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1789_, v_msg_1790_, v_declHint_1791_, v___y_1792_, v___y_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1796_, lean_object* v_ref_1797_, lean_object* v_msg_1798_, lean_object* v_declHint_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1796_, v_ref_1797_, v_msg_1798_, v_declHint_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v_ref_1797_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_1804_, lean_object* v_declHint_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1804_, v_declHint_1805_, v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_1810_, lean_object* v_declHint_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_1810_, v_declHint_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1816_, lean_object* v_ref_1817_, lean_object* v_msg_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1817_, v_msg_1818_, v___y_1819_, v___y_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1823_, lean_object* v_ref_1824_, lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1823_, v_ref_1824_, v_msg_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_ref_1824_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_1830_, lean_object* v_msg_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1831_, v___y_1832_, v___y_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_1836_, v_msg_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t v_useErrorFormat_1842_, lean_object* v_filePath_1843_, size_t v_sz_1844_, size_t v_i_1845_, lean_object* v_bs_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_usize_dec_lt(v_i_1845_, v_sz_1844_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
lean_dec_ref(v_filePath_1843_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_bs_1846_);
return v___x_1851_;
}
else
{
lean_object* v_v_1852_; lean_object* v_fst_1853_; lean_object* v_snd_1854_; lean_object* v___x_1855_; 
v_v_1852_ = lean_array_uget_borrowed(v_bs_1846_, v_i_1845_);
v_fst_1853_ = lean_ctor_get(v_v_1852_, 0);
v_snd_1854_ = lean_ctor_get(v_v_1852_, 1);
lean_inc_ref(v_filePath_1843_);
lean_inc(v_snd_1854_);
lean_inc(v_fst_1853_);
v___x_1855_ = l_Lean_Linter_EnvLinter_printWarning(v_fst_1853_, v_snd_1854_, v_useErrorFormat_1842_, v_filePath_1843_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1846_, v_i_1845_, v___x_1857_);
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = lean_usize_add(v_i_1845_, v___x_1859_);
v___x_1861_ = lean_array_uset(v_bs_x27_1858_, v_i_1845_, v_a_1856_);
v_i_1845_ = v___x_1860_;
v_bs_1846_ = v___x_1861_;
goto _start;
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_bs_1846_);
lean_dec_ref(v_filePath_1843_);
v_a_1863_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1855_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1855_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object* v_useErrorFormat_1871_, lean_object* v_filePath_1872_, lean_object* v_sz_1873_, lean_object* v_i_1874_, lean_object* v_bs_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v_useErrorFormat_boxed_1879_; size_t v_sz_boxed_1880_; size_t v_i_boxed_1881_; lean_object* v_res_1882_; 
v_useErrorFormat_boxed_1879_ = lean_unbox(v_useErrorFormat_1871_);
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1873_);
lean_dec(v_sz_1873_);
v_i_boxed_1881_ = lean_unbox_usize(v_i_1874_);
lean_dec(v_i_1874_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_boxed_1879_, v_filePath_1872_, v_sz_boxed_1880_, v_i_boxed_1881_, v_bs_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1882_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_box(1);
v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object* v_results_1885_, lean_object* v_filePath_1886_, uint8_t v_useErrorFormat_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1885_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; size_t v_sz_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v_sz_1893_ = lean_array_size(v_a_1892_);
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_1887_, v_filePath_1886_, v_sz_1893_, v___x_1894_, v_a_1892_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1906_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1900_ = lean_array_to_list(v_a_1896_);
v___x_1901_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_1902_ = l_Lean_MessageData_joinSep(v___x_1900_, v___x_1901_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1902_);
v___x_1904_ = v___x_1898_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1895_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1895_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v_filePath_1886_);
v_a_1915_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1891_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1891_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object* v_results_1923_, lean_object* v_filePath_1924_, lean_object* v_useErrorFormat_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
uint8_t v_useErrorFormat_boxed_1929_; lean_object* v_res_1930_; 
v_useErrorFormat_boxed_1929_ = lean_unbox(v_useErrorFormat_1925_);
v_res_1930_ = l_Lean_Linter_EnvLinter_printWarnings(v_results_1923_, v_filePath_1924_, v_useErrorFormat_boxed_1929_, v_a_1926_, v_a_1927_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec_ref(v_results_1923_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object* v_x_1931_, lean_object* v_x_1932_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
return v_x_1931_;
}
else
{
lean_object* v_key_1933_; lean_object* v_value_1934_; lean_object* v_tail_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_key_1933_ = lean_ctor_get(v_x_1932_, 0);
v_value_1934_ = lean_ctor_get(v_x_1932_, 1);
v_tail_1935_ = lean_ctor_get(v_x_1932_, 2);
lean_inc(v_value_1934_);
lean_inc(v_key_1933_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_key_1933_);
lean_ctor_set(v___x_1936_, 1, v_value_1934_);
v___x_1937_ = lean_array_push(v_x_1931_, v___x_1936_);
v_x_1931_ = v___x_1937_;
v_x_1932_ = v_tail_1935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_x_1939_, v_x_1940_);
lean_dec(v_x_1940_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object* v_as_1942_, size_t v_i_1943_, size_t v_stop_1944_, lean_object* v_b_1945_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_usize_dec_eq(v_i_1943_, v_stop_1944_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; 
v___x_1947_ = lean_array_uget_borrowed(v_as_1942_, v_i_1943_);
v___x_1948_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_b_1945_, v___x_1947_);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1943_, v___x_1949_);
v_i_1943_ = v___x_1950_;
v_b_1945_ = v___x_1948_;
goto _start;
}
else
{
return v_b_1945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object* v_as_1952_, lean_object* v_i_1953_, lean_object* v_stop_1954_, lean_object* v_b_1955_){
_start:
{
size_t v_i_boxed_1956_; size_t v_stop_boxed_1957_; lean_object* v_res_1958_; 
v_i_boxed_1956_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_stop_boxed_1957_ = lean_unbox_usize(v_stop_1954_);
lean_dec(v_stop_1954_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_as_1952_, v_i_boxed_1956_, v_stop_boxed_1957_, v_b_1955_);
lean_dec_ref(v_as_1952_);
return v_res_1958_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0));
v___x_1961_ = l_Lean_stringToMessageData(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2));
v___x_1964_ = l_Lean_stringToMessageData(v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t v_useErrorFormat_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = l_List_reverse___redArg(v_x_1967_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
else
{
lean_object* v_head_1973_; lean_object* v_tail_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2017_; 
v_head_1973_ = lean_ctor_get(v_x_1966_, 0);
v_tail_1974_ = lean_ctor_get(v_x_1966_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_x_1966_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1976_ = v_x_1966_;
v_isShared_1977_ = v_isSharedCheck_2017_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_tail_1974_);
lean_inc(v_head_1973_);
lean_dec(v_x_1966_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2017_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_a_1979_; lean_object* v_snd_1984_; lean_object* v_fst_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2016_; 
v_snd_1984_ = lean_ctor_get(v_head_1973_, 1);
v_fst_1985_ = lean_ctor_get(v_head_1973_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_head_1973_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1987_ = v_head_1973_;
v_isShared_1988_ = v_isSharedCheck_2016_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snd_1984_);
lean_inc(v_fst_1985_);
lean_dec(v_head_1973_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2016_;
goto v_resetjp_1986_;
}
v___jp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_x_1967_);
lean_ctor_set(v___x_1976_, 0, v_a_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1979_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_x_1967_);
v___x_1981_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
v_x_1966_ = v_tail_1974_;
v_x_1967_ = v___x_1981_;
goto _start;
}
}
v_resetjp_1986_:
{
lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2015_; 
v_fst_1989_ = lean_ctor_get(v_snd_1984_, 0);
v_snd_1990_ = lean_ctor_get(v_snd_1984_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_snd_1984_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1992_ = v_snd_1984_;
v_isShared_1993_ = v_isSharedCheck_2015_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_snd_1990_);
lean_inc(v_fst_1989_);
lean_dec(v_snd_1984_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2015_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_1990_, v_fst_1989_, v_useErrorFormat_1965_, v___y_1968_, v___y_1969_);
lean_dec(v_snd_1990_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v___x_1996_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1);
v___x_1997_ = l_Lean_MessageData_ofName(v_fst_1985_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 7);
lean_ctor_set(v___x_1992_, 1, v___x_1997_);
lean_ctor_set(v___x_1992_, 0, v___x_1996_);
v___x_1999_ = v___x_1992_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 7);
lean_ctor_set(v___x_1987_, 1, v___x_2000_);
lean_ctor_set(v___x_1987_, 0, v___x_1999_);
v___x_2002_ = v___x_1987_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v_a_1995_);
v_a_1979_ = v___x_2003_;
goto v___jp_1978_;
}
}
}
else
{
lean_del_object(v___x_1992_);
lean_del_object(v___x_1987_);
lean_dec(v_fst_1985_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_1994_, 1);
v_a_1979_ = v_a_2006_;
goto v___jp_1978_;
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_del_object(v___x_1976_);
lean_dec(v_tail_1974_);
lean_dec(v_x_1967_);
v_a_2007_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1994_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1994_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object* v_useErrorFormat_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_useErrorFormat_boxed_2024_; lean_object* v_res_2025_; 
v_useErrorFormat_boxed_2024_ = lean_unbox(v_useErrorFormat_2018_);
v_res_2025_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_boxed_2024_, v_x_2019_, v_x_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object* v_a_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_box(0);
return v___x_2028_;
}
else
{
lean_object* v_key_2029_; lean_object* v_value_2030_; lean_object* v_tail_2031_; uint8_t v___x_2032_; 
v_key_2029_ = lean_ctor_get(v_x_2027_, 0);
v_value_2030_ = lean_ctor_get(v_x_2027_, 1);
v_tail_2031_ = lean_ctor_get(v_x_2027_, 2);
v___x_2032_ = lean_name_eq(v_key_2029_, v_a_2026_);
if (v___x_2032_ == 0)
{
v_x_2027_ = v_tail_2031_;
goto _start;
}
else
{
lean_object* v___x_2034_; 
lean_inc(v_value_2030_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_value_2030_);
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object* v_a_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2035_, v_x_2036_);
lean_dec(v_x_2036_);
lean_dec(v_a_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object* v_m_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_buckets_2040_; lean_object* v___x_2041_; uint64_t v___y_2043_; 
v_buckets_2040_ = lean_ctor_get(v_m_2038_, 1);
v___x_2041_ = lean_array_get_size(v_buckets_2040_);
if (lean_obj_tag(v_a_2039_) == 0)
{
uint64_t v___x_2057_; 
v___x_2057_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_2043_ = v___x_2057_;
goto v___jp_2042_;
}
else
{
uint64_t v_hash_2058_; 
v_hash_2058_ = lean_ctor_get_uint64(v_a_2039_, sizeof(void*)*2);
v___y_2043_ = v_hash_2058_;
goto v___jp_2042_;
}
v___jp_2042_:
{
uint64_t v___x_2044_; uint64_t v___x_2045_; uint64_t v_fold_2046_; uint64_t v___x_2047_; uint64_t v___x_2048_; uint64_t v___x_2049_; size_t v___x_2050_; size_t v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2044_ = 32ULL;
v___x_2045_ = lean_uint64_shift_right(v___y_2043_, v___x_2044_);
v_fold_2046_ = lean_uint64_xor(v___y_2043_, v___x_2045_);
v___x_2047_ = 16ULL;
v___x_2048_ = lean_uint64_shift_right(v_fold_2046_, v___x_2047_);
v___x_2049_ = lean_uint64_xor(v_fold_2046_, v___x_2048_);
v___x_2050_ = lean_uint64_to_usize(v___x_2049_);
v___x_2051_ = lean_usize_of_nat(v___x_2041_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_sub(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_usize_land(v___x_2050_, v___x_2053_);
v___x_2055_ = lean_array_uget_borrowed(v_buckets_2040_, v___x_2054_);
v___x_2056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2039_, v___x_2055_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object* v_m_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_m_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object* v_key_2062_, lean_object* v_value_2063_, lean_object* v_fp_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v___x_2068_, v_key_2062_, v_value_2063_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_fp_2064_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object* v_key_2072_, lean_object* v_value_2073_, lean_object* v_fp_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2072_, v_value_2073_, v_fp_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object* v_constName_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v_env_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2083_ = lean_st_ref_get(v___y_2081_);
v_env_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc_ref(v_env_2084_);
lean_dec(v___x_2083_);
v___x_2085_ = 0;
lean_inc(v_constName_2079_);
v___x_2086_ = l_Lean_Environment_find_x3f(v_env_2084_, v_constName_2079_, v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_2079_, v___y_2080_, v___y_2081_);
return v___x_2087_;
}
else
{
lean_object* v_val_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_constName_2079_);
v_val_2088_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_val_2088_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 0);
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_val_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object* v_constName_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_constName_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object* v_declName_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
lean_inc(v_declName_2101_);
v___x_2105_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_declName_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2132_; 
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2133_);
v___x_2107_ = v___x_2105_;
v_isShared_2108_ = v_isSharedCheck_2132_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v___x_2105_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2132_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v_env_2110_; lean_object* v___x_2111_; 
v___x_2109_ = lean_st_ref_get(v___y_2103_);
v_env_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_ref(v_env_2110_);
lean_dec(v___x_2109_);
v___x_2111_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2110_, v_declName_2101_);
lean_dec(v_declName_2101_);
lean_dec_ref(v_env_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = lean_box(0);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2112_);
v___x_2114_ = v___x_2107_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
else
{
lean_object* v_val_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2131_; 
v_val_2116_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2118_ = v___x_2111_;
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_val_2116_);
lean_dec(v___x_2111_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v_env_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2120_ = lean_st_ref_get(v___y_2103_);
v_env_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc_ref(v_env_2121_);
lean_dec(v___x_2120_);
v___x_2122_ = lean_box(0);
v___x_2123_ = l_Lean_Environment_allImportedModuleNames(v_env_2121_);
lean_dec_ref(v_env_2121_);
v___x_2124_ = lean_array_get(v___x_2122_, v___x_2123_, v_val_2116_);
lean_dec(v_val_2116_);
lean_dec_ref(v___x_2123_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2124_);
v___x_2126_ = v___x_2118_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2126_);
v___x_2128_ = v___x_2107_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_declName_2101_);
v_a_2134_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2105_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2105_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object* v_declName_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_declName_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t v_useErrorFormat_2150_, lean_object* v_sp_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_sp_2151_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_x_2152_);
return v___x_2157_;
}
else
{
lean_object* v_key_2158_; lean_object* v_value_2159_; lean_object* v_tail_2160_; lean_object* v___y_2162_; lean_object* v_a_2163_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___x_2170_; 
v_key_2158_ = lean_ctor_get(v_x_2153_, 0);
lean_inc_n(v_key_2158_, 2);
v_value_2159_ = lean_ctor_get(v_x_2153_, 1);
lean_inc(v_value_2159_);
v_tail_2160_ = lean_ctor_get(v_x_2153_, 2);
lean_inc(v_tail_2160_);
lean_dec_ref_known(v_x_2153_, 3);
v___x_2170_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_key_2158_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___y_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = lean_st_ref_get(v___y_2155_);
if (lean_obj_tag(v_a_2171_) == 0)
{
lean_object* v_env_2210_; lean_object* v___x_2211_; 
v_env_2210_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_ref(v_env_2210_);
lean_dec(v___x_2172_);
v___x_2211_ = l_Lean_Environment_mainModule(v_env_2210_);
lean_dec_ref(v_env_2210_);
v___y_2174_ = v___x_2211_;
goto v___jp_2173_;
}
else
{
lean_object* v_val_2212_; 
lean_dec(v___x_2172_);
v_val_2212_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v_a_2171_, 1);
v___y_2174_ = v_val_2212_;
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_x_2152_, v___y_2174_);
if (lean_obj_tag(v___x_2175_) == 0)
{
if (v_useErrorFormat_2150_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2177_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2158_, v_value_2159_, v___x_2176_, v___y_2154_, v___y_2155_);
v___y_2167_ = v___y_2174_;
v___y_2168_ = v___x_2177_;
goto v___jp_2166_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1));
lean_inc(v___y_2174_);
lean_inc(v_sp_2151_);
v___x_2179_ = l_Lean_SearchPath_findWithExt(v_sp_2151_, v___x_2178_, v___y_2174_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
if (lean_obj_tag(v_a_2180_) == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2));
lean_inc(v___y_2174_);
v___x_2182_ = l_Lean_modToFilePath(v___x_2181_, v___y_2174_, v___x_2178_);
v___x_2183_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2158_, v_value_2159_, v___x_2182_, v___y_2154_, v___y_2155_);
v___y_2167_ = v___y_2174_;
v___y_2168_ = v___x_2183_;
goto v___jp_2166_;
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2185_; 
v_val_2184_ = lean_ctor_get(v_a_2180_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_a_2180_, 1);
v___x_2185_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2158_, v_value_2159_, v_val_2184_, v___y_2154_, v___y_2155_);
v___y_2167_ = v___y_2174_;
v___y_2168_ = v___x_2185_;
goto v___jp_2166_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v___y_2174_);
lean_dec(v_tail_2160_);
lean_dec(v_value_2159_);
lean_dec(v_key_2158_);
lean_dec_ref(v_x_2152_);
lean_dec(v_sp_2151_);
v_a_2186_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2188_ = v___x_2179_;
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2179_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_ref_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v_ref_2190_ = lean_ctor_get(v___y_2154_, 5);
v___x_2191_ = lean_io_error_to_string(v_a_2186_);
v___x_2192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
v___x_2193_ = l_Lean_MessageData_ofFormat(v___x_2192_);
lean_inc(v_ref_2190_);
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_ref_2190_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
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
}
else
{
lean_object* v_val_2199_; lean_object* v_fst_2200_; lean_object* v_snd_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2209_; 
v_val_2199_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v___x_2175_, 1);
v_fst_2200_ = lean_ctor_get(v_val_2199_, 0);
v_snd_2201_ = lean_ctor_get(v_val_2199_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_val_2199_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2203_ = v_val_2199_;
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_snd_2201_);
lean_inc(v_fst_2200_);
lean_dec(v_val_2199_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_snd_2201_, v_key_2158_, v_value_2159_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v___x_2205_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_fst_2200_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
v___y_2162_ = v___y_2174_;
v_a_2163_ = v___x_2207_;
goto v___jp_2161_;
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_tail_2160_);
lean_dec(v_value_2159_);
lean_dec(v_key_2158_);
lean_dec_ref(v_x_2152_);
lean_dec(v_sp_2151_);
v_a_2213_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2170_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2170_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
v___jp_2161_:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_x_2152_, v___y_2162_, v_a_2163_);
v_x_2152_ = v___x_2164_;
v_x_2153_ = v_tail_2160_;
goto _start;
}
v___jp_2166_:
{
lean_object* v_a_2169_; 
v_a_2169_ = lean_ctor_get(v___y_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___y_2168_);
v___y_2162_ = v___y_2167_;
v_a_2163_ = v_a_2169_;
goto v___jp_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object* v_useErrorFormat_2221_, lean_object* v_sp_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v_useErrorFormat_boxed_2228_; lean_object* v_res_2229_; 
v_useErrorFormat_boxed_2228_ = lean_unbox(v_useErrorFormat_2221_);
v_res_2229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_boxed_2228_, v_sp_2222_, v_x_2223_, v_x_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t v_useErrorFormat_2230_, lean_object* v_sp_2231_, lean_object* v_as_2232_, size_t v_i_2233_, size_t v_stop_2234_, lean_object* v_b_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_usize_dec_eq(v_i_2233_, v_stop_2234_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_array_uget_borrowed(v_as_2232_, v_i_2233_);
lean_inc(v___x_2240_);
lean_inc(v_sp_2231_);
v___x_2241_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_2230_, v_sp_2231_, v_b_2235_, v___x_2240_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; size_t v___x_2243_; size_t v___x_2244_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2233_, v___x_2243_);
v_i_2233_ = v___x_2244_;
v_b_2235_ = v_a_2242_;
goto _start;
}
else
{
lean_dec(v_sp_2231_);
return v___x_2241_;
}
}
else
{
lean_object* v___x_2246_; 
lean_dec(v_sp_2231_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_b_2235_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object* v_useErrorFormat_2247_, lean_object* v_sp_2248_, lean_object* v_as_2249_, lean_object* v_i_2250_, lean_object* v_stop_2251_, lean_object* v_b_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v_useErrorFormat_boxed_2256_; size_t v_i_boxed_2257_; size_t v_stop_boxed_2258_; lean_object* v_res_2259_; 
v_useErrorFormat_boxed_2256_ = lean_unbox(v_useErrorFormat_2247_);
v_i_boxed_2257_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_stop_boxed_2258_ = lean_unbox_usize(v_stop_2251_);
lean_dec(v_stop_2251_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_boxed_2256_, v_sp_2248_, v_as_2249_, v_i_boxed_2257_, v_stop_boxed_2258_, v_b_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_as_2249_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object* v_hi_2260_, lean_object* v_pivot_2261_, lean_object* v_as_2262_, lean_object* v_i_2263_, lean_object* v_k_2264_){
_start:
{
uint8_t v___x_2265_; 
v___x_2265_ = lean_nat_dec_lt(v_k_2264_, v_hi_2260_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v_k_2264_);
lean_dec_ref(v_pivot_2261_);
v___x_2266_ = lean_array_fswap(v_as_2262_, v_i_2263_, v_hi_2260_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_i_2263_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; lean_object* v_fst_2269_; lean_object* v_fst_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2268_ = lean_array_fget_borrowed(v_as_2262_, v_k_2264_);
v_fst_2269_ = lean_ctor_get(v___x_2268_, 0);
v_fst_2270_ = lean_ctor_get(v_pivot_2261_, 0);
lean_inc(v_fst_2269_);
v___x_2271_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2269_, v___x_2265_);
lean_inc(v_fst_2270_);
v___x_2272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2270_, v___x_2265_);
v___x_2273_ = lean_string_dec_lt(v___x_2271_, v___x_2272_);
lean_dec_ref(v___x_2272_);
lean_dec_ref(v___x_2271_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_nat_add(v_k_2264_, v___x_2274_);
lean_dec(v_k_2264_);
v_k_2264_ = v___x_2275_;
goto _start;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2277_ = lean_array_fswap(v_as_2262_, v_i_2263_, v_k_2264_);
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_nat_add(v_i_2263_, v___x_2278_);
lean_dec(v_i_2263_);
v___x_2280_ = lean_nat_add(v_k_2264_, v___x_2278_);
lean_dec(v_k_2264_);
v_as_2262_ = v___x_2277_;
v_i_2263_ = v___x_2279_;
v_k_2264_ = v___x_2280_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object* v_hi_2282_, lean_object* v_pivot_2283_, lean_object* v_as_2284_, lean_object* v_i_2285_, lean_object* v_k_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2282_, v_pivot_2283_, v_as_2284_, v_i_2285_, v_k_2286_);
lean_dec(v_hi_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t v___x_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v_fst_2291_; lean_object* v_fst_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_fst_2291_ = lean_ctor_get(v_x_2289_, 0);
lean_inc(v_fst_2291_);
lean_dec_ref(v_x_2289_);
v_fst_2292_ = lean_ctor_get(v_x_2290_, 0);
lean_inc(v_fst_2292_);
lean_dec_ref(v_x_2290_);
v___x_2293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2291_, v___x_2288_);
v___x_2294_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2292_, v___x_2288_);
v___x_2295_ = lean_string_dec_lt(v___x_2293_, v___x_2294_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___x_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object* v___x_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v___x_5444__boxed_2299_; uint8_t v_res_2300_; lean_object* v_r_2301_; 
v___x_5444__boxed_2299_ = lean_unbox(v___x_2296_);
v_res_2300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_5444__boxed_2299_, v_x_2297_, v_x_2298_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object* v_n_2302_, lean_object* v_as_2303_, lean_object* v_lo_2304_, lean_object* v_hi_2305_){
_start:
{
lean_object* v___y_2307_; uint8_t v___x_2317_; 
v___x_2317_ = lean_nat_dec_lt(v_lo_2304_, v_hi_2305_);
if (v___x_2317_ == 0)
{
lean_dec(v_lo_2304_);
return v_as_2303_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v_mid_2320_; lean_object* v___y_2322_; lean_object* v___y_2328_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2318_ = lean_nat_add(v_lo_2304_, v_hi_2305_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v_mid_2320_ = lean_nat_shiftr(v___x_2318_, v___x_2319_);
lean_dec(v___x_2318_);
v___x_2333_ = lean_array_fget_borrowed(v_as_2303_, v_mid_2320_);
v___x_2334_ = lean_array_fget_borrowed(v_as_2303_, v_lo_2304_);
lean_inc(v___x_2334_);
lean_inc(v___x_2333_);
v___x_2335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2317_, v___x_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
v___y_2328_ = v_as_2303_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_array_fswap(v_as_2303_, v_lo_2304_, v_mid_2320_);
v___y_2328_ = v___x_2336_;
goto v___jp_2327_;
}
v___jp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2323_ = lean_array_fget_borrowed(v___y_2322_, v_mid_2320_);
v___x_2324_ = lean_array_fget_borrowed(v___y_2322_, v_hi_2305_);
lean_inc(v___x_2324_);
lean_inc(v___x_2323_);
v___x_2325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2317_, v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec(v_mid_2320_);
v___y_2307_ = v___y_2322_;
goto v___jp_2306_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_array_fswap(v___y_2322_, v_mid_2320_, v_hi_2305_);
lean_dec(v_mid_2320_);
v___y_2307_ = v___x_2326_;
goto v___jp_2306_;
}
}
v___jp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = lean_array_fget_borrowed(v___y_2328_, v_hi_2305_);
v___x_2330_ = lean_array_fget_borrowed(v___y_2328_, v_lo_2304_);
lean_inc(v___x_2330_);
lean_inc(v___x_2329_);
v___x_2331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2317_, v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
v___y_2322_ = v___y_2328_;
goto v___jp_2321_;
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_array_fswap(v___y_2328_, v_lo_2304_, v_hi_2305_);
v___y_2322_ = v___x_2332_;
goto v___jp_2321_;
}
}
}
v___jp_2306_:
{
lean_object* v_pivot_2308_; lean_object* v___x_2309_; lean_object* v_fst_2310_; lean_object* v_snd_2311_; uint8_t v___x_2312_; 
v_pivot_2308_ = lean_array_fget(v___y_2307_, v_hi_2305_);
lean_inc_n(v_lo_2304_, 2);
v___x_2309_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2305_, v_pivot_2308_, v___y_2307_, v_lo_2304_, v_lo_2304_);
v_fst_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_fst_2310_);
v_snd_2311_ = lean_ctor_get(v___x_2309_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2309_);
v___x_2312_ = lean_nat_dec_le(v_hi_2305_, v_fst_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2302_, v_snd_2311_, v_lo_2304_, v_fst_2310_);
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_nat_add(v_fst_2310_, v___x_2314_);
lean_dec(v_fst_2310_);
v_as_2303_ = v___x_2313_;
v_lo_2304_ = v___x_2315_;
goto _start;
}
else
{
lean_dec(v_fst_2310_);
lean_dec(v_lo_2304_);
return v_snd_2311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object* v_n_2337_, lean_object* v_as_2338_, lean_object* v_lo_2339_, lean_object* v_hi_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2337_, v_as_2338_, v_lo_2339_, v_hi_2340_);
lean_dec(v_hi_2340_);
lean_dec(v_n_2337_);
return v_res_2341_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object* v_results_2344_, uint8_t v_useErrorFormat_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v_size_2403_; lean_object* v_buckets_2404_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v_sp_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; 
if (v_useErrorFormat_2345_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_box(0);
v_sp_2432_ = v___x_2448_;
v___y_2433_ = v_a_2346_;
v___y_2434_ = v_a_2347_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_sp_2432_ = v_a_2450_;
v___y_2433_ = v_a_2346_;
v___y_2434_ = v_a_2347_;
goto v___jp_2431_;
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2463_; 
v_a_2451_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2453_ = v___x_2449_;
v_isShared_2454_ = v_isSharedCheck_2463_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2463_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_ref_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v_ref_2455_ = lean_ctor_get(v_a_2346_, 5);
v___x_2456_ = lean_io_error_to_string(v_a_2451_);
v___x_2457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
v___x_2458_ = l_Lean_MessageData_ofFormat(v___x_2457_);
lean_inc(v_ref_2455_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v_ref_2455_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2459_);
v___x_2461_ = v___x_2453_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
v___jp_2349_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_array_to_list(v___y_2352_);
v___x_2354_ = lean_box(0);
v___x_2355_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_2345_, v___x_2353_, v___x_2354_, v___y_2351_, v___y_2350_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2365_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2365_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2365_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2360_ = lean_obj_once(&l_Lean_Linter_EnvLinter_groupedByFilename___closed__0, &l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once, _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0);
v___x_2361_ = l_Lean_MessageData_joinSep(v_a_2356_, v___x_2360_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2361_);
v___x_2363_ = v___x_2358_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
v_a_2366_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2355_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2355_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
v___jp_2374_:
{
lean_object* v___x_2381_; 
v___x_2381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v___y_2375_, v___y_2377_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec(v___y_2375_);
v___y_2350_ = v___y_2376_;
v___y_2351_ = v___y_2378_;
v___y_2352_ = v___x_2381_;
goto v___jp_2349_;
}
v___jp_2382_:
{
uint8_t v___x_2389_; 
v___x_2389_ = lean_nat_dec_le(v___y_2388_, v___y_2384_);
if (v___x_2389_ == 0)
{
lean_dec(v___y_2384_);
lean_inc(v___y_2388_);
v___y_2375_ = v___y_2383_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2385_;
v___y_2378_ = v___y_2387_;
v___y_2379_ = v___y_2388_;
v___y_2380_ = v___y_2388_;
goto v___jp_2374_;
}
else
{
v___y_2375_ = v___y_2383_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2385_;
v___y_2378_ = v___y_2387_;
v___y_2379_ = v___y_2388_;
v___y_2380_ = v___y_2384_;
goto v___jp_2374_;
}
}
v___jp_2390_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2394_ = lean_array_get_size(v___y_2393_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2396_ = lean_nat_dec_eq(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_sub(v___x_2394_, v___x_2397_);
v___x_2399_ = lean_nat_dec_le(v___x_2395_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_inc(v___x_2398_);
v___y_2383_ = v___x_2394_;
v___y_2384_ = v___x_2398_;
v___y_2385_ = v___y_2393_;
v___y_2386_ = v___y_2391_;
v___y_2387_ = v___y_2392_;
v___y_2388_ = v___x_2398_;
goto v___jp_2382_;
}
else
{
v___y_2383_ = v___x_2394_;
v___y_2384_ = v___x_2398_;
v___y_2385_ = v___y_2393_;
v___y_2386_ = v___y_2391_;
v___y_2387_ = v___y_2392_;
v___y_2388_ = v___x_2395_;
goto v___jp_2382_;
}
}
else
{
v___y_2350_ = v___y_2391_;
v___y_2351_ = v___y_2392_;
v___y_2352_ = v___y_2393_;
goto v___jp_2349_;
}
}
v___jp_2400_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2405_ = lean_mk_empty_array_with_capacity(v_size_2403_);
lean_dec(v_size_2403_);
v___x_2406_ = lean_unsigned_to_nat(0u);
v___x_2407_ = lean_array_get_size(v_buckets_2404_);
v___x_2408_ = lean_nat_dec_lt(v___x_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v_buckets_2404_);
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___x_2405_;
goto v___jp_2390_;
}
else
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
if (v___x_2409_ == 0)
{
if (v___x_2408_ == 0)
{
lean_dec_ref(v_buckets_2404_);
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___x_2405_;
goto v___jp_2390_;
}
else
{
size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = lean_usize_of_nat(v___x_2407_);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2404_, v___x_2410_, v___x_2411_, v___x_2405_);
lean_dec_ref(v_buckets_2404_);
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___x_2412_;
goto v___jp_2390_;
}
}
else
{
size_t v___x_2413_; size_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = ((size_t)0ULL);
v___x_2414_ = lean_usize_of_nat(v___x_2407_);
v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2404_, v___x_2413_, v___x_2414_, v___x_2405_);
lean_dec_ref(v_buckets_2404_);
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___x_2415_;
goto v___jp_2390_;
}
}
}
v___jp_2416_:
{
if (lean_obj_tag(v___y_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v_size_2421_; lean_object* v_buckets_2422_; 
v_a_2420_ = lean_ctor_get(v___y_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___y_2419_, 1);
v_size_2421_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_size_2421_);
v_buckets_2422_ = lean_ctor_get(v_a_2420_, 1);
lean_inc_ref(v_buckets_2422_);
lean_dec(v_a_2420_);
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2418_;
v_size_2403_ = v_size_2421_;
v_buckets_2404_ = v_buckets_2422_;
goto v___jp_2400_;
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
v_a_2423_ = lean_ctor_get(v___y_2419_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___y_2419_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___y_2419_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___y_2419_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
v___jp_2431_:
{
lean_object* v_buckets_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_buckets_2435_ = lean_ctor_get(v_results_2344_, 1);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0);
v___x_2438_ = lean_array_get_size(v_buckets_2435_);
v___x_2439_ = lean_nat_dec_lt(v___x_2436_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_dec(v_sp_2432_);
v___y_2401_ = v___y_2434_;
v___y_2402_ = v___y_2433_;
v_size_2403_ = v___x_2436_;
v_buckets_2404_ = v___x_2437_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v___x_2441_ = lean_nat_dec_le(v___x_2438_, v___x_2438_);
if (v___x_2441_ == 0)
{
if (v___x_2439_ == 0)
{
lean_dec(v_sp_2432_);
v___y_2401_ = v___y_2434_;
v___y_2402_ = v___y_2433_;
v_size_2403_ = v___x_2436_;
v_buckets_2404_ = v___x_2437_;
goto v___jp_2400_;
}
else
{
size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = lean_usize_of_nat(v___x_2438_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2345_, v_sp_2432_, v_buckets_2435_, v___x_2442_, v___x_2443_, v___x_2440_, v___y_2433_, v___y_2434_);
v___y_2417_ = v___y_2434_;
v___y_2418_ = v___y_2433_;
v___y_2419_ = v___x_2444_;
goto v___jp_2416_;
}
}
else
{
size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = lean_usize_of_nat(v___x_2438_);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2345_, v_sp_2432_, v_buckets_2435_, v___x_2445_, v___x_2446_, v___x_2440_, v___y_2433_, v___y_2434_);
v___y_2417_ = v___y_2434_;
v___y_2418_ = v___y_2433_;
v___y_2419_ = v___x_2447_;
goto v___jp_2416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object* v_results_2464_, lean_object* v_useErrorFormat_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
uint8_t v_useErrorFormat_boxed_2469_; lean_object* v_res_2470_; 
v_useErrorFormat_boxed_2469_ = lean_unbox(v_useErrorFormat_2465_);
v_res_2470_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_results_2464_, v_useErrorFormat_boxed_2469_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec_ref(v_results_2464_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object* v_n_2471_, lean_object* v_as_2472_, lean_object* v_lo_2473_, lean_object* v_hi_2474_, lean_object* v_w_2475_, lean_object* v_hlo_2476_, lean_object* v_hhi_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2471_, v_as_2472_, v_lo_2473_, v_hi_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object* v_n_2479_, lean_object* v_as_2480_, lean_object* v_lo_2481_, lean_object* v_hi_2482_, lean_object* v_w_2483_, lean_object* v_hlo_2484_, lean_object* v_hhi_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(v_n_2479_, v_as_2480_, v_lo_2481_, v_hi_2482_, v_w_2483_, v_hlo_2484_, v_hhi_2485_);
lean_dec(v_hi_2482_);
lean_dec(v_n_2479_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object* v_00_u03b2_2487_, lean_object* v_m_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2488_, v_a_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object* v_00_u03b2_2491_, lean_object* v_m_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(v_00_u03b2_2491_, v_m_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_m_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object* v_n_2495_, lean_object* v_lo_2496_, lean_object* v_hi_2497_, lean_object* v_hhi_2498_, lean_object* v_pivot_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_k_2502_, lean_object* v_ilo_2503_, lean_object* v_ik_2504_, lean_object* v_w_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2497_, v_pivot_2499_, v_as_2500_, v_i_2501_, v_k_2502_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object* v_n_2507_, lean_object* v_lo_2508_, lean_object* v_hi_2509_, lean_object* v_hhi_2510_, lean_object* v_pivot_2511_, lean_object* v_as_2512_, lean_object* v_i_2513_, lean_object* v_k_2514_, lean_object* v_ilo_2515_, lean_object* v_ik_2516_, lean_object* v_w_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(v_n_2507_, v_lo_2508_, v_hi_2509_, v_hhi_2510_, v_pivot_2511_, v_as_2512_, v_i_2513_, v_k_2514_, v_ilo_2515_, v_ik_2516_, v_w_2517_);
lean_dec(v_hi_2509_);
lean_dec(v_lo_2508_);
lean_dec(v_n_2507_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object* v_00_u03b2_2519_, lean_object* v_a_2520_, lean_object* v_x_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2520_, v_x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2523_, lean_object* v_a_2524_, lean_object* v_x_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(v_00_u03b2_2523_, v_a_2524_, v_x_2525_);
lean_dec(v_x_2525_);
lean_dec(v_a_2524_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_bs_2529_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2530_ == 0)
{
return v_bs_2529_;
}
else
{
lean_object* v_v_2531_; lean_object* v_snd_2532_; lean_object* v_size_2533_; lean_object* v___x_2534_; lean_object* v_bs_x27_2535_; size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v_v_2531_ = lean_array_uget_borrowed(v_bs_2529_, v_i_2528_);
v_snd_2532_ = lean_ctor_get(v_v_2531_, 1);
v_size_2533_ = lean_ctor_get(v_snd_2532_, 0);
lean_inc(v_size_2533_);
v___x_2534_ = lean_unsigned_to_nat(0u);
v_bs_x27_2535_ = lean_array_uset(v_bs_2529_, v_i_2528_, v___x_2534_);
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_add(v_i_2528_, v___x_2536_);
v___x_2538_ = lean_array_uset(v_bs_x27_2535_, v_i_2528_, v_size_2533_);
v_i_2528_ = v___x_2537_;
v_bs_2529_ = v___x_2538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object* v_sz_2540_, lean_object* v_i_2541_, lean_object* v_bs_2542_){
_start:
{
size_t v_sz_boxed_2543_; size_t v_i_boxed_2544_; lean_object* v_res_2545_; 
v_sz_boxed_2543_ = lean_unbox_usize(v_sz_2540_);
lean_dec(v_sz_2540_);
v_i_boxed_2544_ = lean_unbox_usize(v_i_2541_);
lean_dec(v_i_2541_);
v_res_2545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_boxed_2543_, v_i_boxed_2544_, v_bs_2542_);
return v_res_2545_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6));
v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t v_useErrorFormat_2558_, uint8_t v_groupByFilename_2559_, uint8_t v_verbose_2560_, lean_object* v_as_2561_, size_t v_i_2562_, size_t v_stop_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_a_2569_; lean_object* v_val_2574_; uint8_t v___x_2576_; 
v___x_2576_ = lean_usize_dec_eq(v_i_2562_, v_stop_2563_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2642_; 
v___x_2577_ = lean_array_uget(v_as_2561_, v_i_2562_);
v_fst_2578_ = lean_ctor_get(v___x_2577_, 0);
v_snd_2579_ = lean_ctor_get(v___x_2577_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2581_ = v___x_2577_;
v_isShared_2582_ = v_isSharedCheck_2642_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_snd_2579_);
lean_inc(v_fst_2578_);
lean_dec(v___x_2577_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2642_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v_warnings_2584_; lean_object* v_size_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_size_2612_ = lean_ctor_get(v_snd_2579_, 0);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_nat_dec_eq(v_size_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
if (v_groupByFilename_2559_ == 0)
{
if (v_useErrorFormat_2558_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2616_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2579_, v___x_2615_, v_useErrorFormat_2558_, v___y_2565_, v___y_2566_);
lean_dec(v_snd_2579_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_warnings_2584_ = v_a_2617_;
goto v___jp_2583_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_del_object(v___x_2581_);
lean_dec(v_fst_2578_);
lean_dec_ref(v_b_2564_);
v_a_2618_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2616_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
goto v___jp_2601_;
}
}
else
{
goto v___jp_2601_;
}
}
else
{
lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2639_; 
lean_del_object(v___x_2581_);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_snd_2579_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; lean_object* v_unused_2641_; 
v_unused_2640_ = lean_ctor_get(v_snd_2579_, 1);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_snd_2579_, 0);
lean_dec(v_unused_2641_);
v___x_2627_ = v_snd_2579_;
v_isShared_2628_ = v_isSharedCheck_2639_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v_snd_2579_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2639_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
uint8_t v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = 2;
v___x_2630_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_verbose_2560_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_del_object(v___x_2627_);
lean_dec(v_fst_2578_);
v_a_2569_ = v_b_2564_;
goto v___jp_2568_;
}
else
{
lean_object* v_toEnvLinter_2631_; lean_object* v_noErrorsFound_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v_toEnvLinter_2631_ = lean_ctor_get(v_fst_2578_, 0);
lean_inc_ref(v_toEnvLinter_2631_);
lean_dec(v_fst_2578_);
v_noErrorsFound_2632_ = lean_ctor_get(v_toEnvLinter_2631_, 1);
lean_inc_ref(v_noErrorsFound_2632_);
lean_dec_ref(v_toEnvLinter_2631_);
v___x_2633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7);
if (v_isShared_2628_ == 0)
{
lean_ctor_set_tag(v___x_2627_, 7);
lean_ctor_set(v___x_2627_, 1, v_noErrorsFound_2632_);
lean_ctor_set(v___x_2627_, 0, v___x_2633_);
v___x_2635_ = v___x_2627_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_noErrorsFound_2632_);
v___x_2635_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v_val_2574_ = v___x_2637_;
goto v___jp_2573_;
}
}
}
}
v___jp_2583_:
{
lean_object* v_toEnvLinter_2585_; lean_object* v_optName_2586_; lean_object* v_errorsFound_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v_toEnvLinter_2585_ = lean_ctor_get(v_fst_2578_, 0);
lean_inc_ref(v_toEnvLinter_2585_);
v_optName_2586_ = lean_ctor_get(v_fst_2578_, 1);
lean_inc(v_optName_2586_);
lean_dec(v_fst_2578_);
v_errorsFound_2587_ = lean_ctor_get(v_toEnvLinter_2585_, 2);
lean_inc_ref(v_errorsFound_2587_);
lean_dec_ref(v_toEnvLinter_2585_);
v___x_2588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1);
v___x_2589_ = l_Lean_MessageData_ofName(v_optName_2586_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 7);
lean_ctor_set(v___x_2581_, 1, v___x_2589_);
lean_ctor_set(v___x_2581_, 0, v___x_2588_);
v___x_2591_ = v___x_2581_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_errorsFound_2587_);
v___x_2595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v_warnings_2584_);
v___x_2598_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v_val_2574_ = v___x_2599_;
goto v___jp_2573_;
}
}
v___jp_2601_:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_snd_2579_, v_useErrorFormat_2558_, v___y_2565_, v___y_2566_);
lean_dec(v_snd_2579_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v_warnings_2584_ = v_a_2603_;
goto v___jp_2583_;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_del_object(v___x_2581_);
lean_dec(v_fst_2578_);
lean_dec_ref(v_b_2564_);
v_a_2604_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2602_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
else
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_b_2564_);
return v___x_2643_;
}
v___jp_2568_:
{
size_t v___x_2570_; size_t v___x_2571_; 
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2562_, v___x_2570_);
v_i_2562_ = v___x_2571_;
v_b_2564_ = v_a_2569_;
goto _start;
}
v___jp_2573_:
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_array_push(v_b_2564_, v_val_2574_);
v_a_2569_ = v___x_2575_;
goto v___jp_2568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object* v_useErrorFormat_2644_, lean_object* v_groupByFilename_2645_, lean_object* v_verbose_2646_, lean_object* v_as_2647_, lean_object* v_i_2648_, lean_object* v_stop_2649_, lean_object* v_b_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
uint8_t v_useErrorFormat_boxed_2654_; uint8_t v_groupByFilename_boxed_2655_; uint8_t v_verbose_boxed_2656_; size_t v_i_boxed_2657_; size_t v_stop_boxed_2658_; lean_object* v_res_2659_; 
v_useErrorFormat_boxed_2654_ = lean_unbox(v_useErrorFormat_2644_);
v_groupByFilename_boxed_2655_ = lean_unbox(v_groupByFilename_2645_);
v_verbose_boxed_2656_ = lean_unbox(v_verbose_2646_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_stop_boxed_2658_ = lean_unbox_usize(v_stop_2649_);
lean_dec(v_stop_2649_);
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_boxed_2654_, v_groupByFilename_boxed_2655_, v_verbose_boxed_2656_, v_as_2647_, v_i_boxed_2657_, v_stop_boxed_2658_, v_b_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec_ref(v_as_2647_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t v_useErrorFormat_2662_, uint8_t v_groupByFilename_2663_, uint8_t v_verbose_2664_, lean_object* v_as_2665_, lean_object* v_start_2666_, lean_object* v_stop_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0));
v___x_2672_ = lean_nat_dec_lt(v_start_2666_, v_stop_2667_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = lean_array_get_size(v_as_2665_);
v___x_2675_ = lean_nat_dec_le(v_stop_2667_, v___x_2674_);
if (v___x_2675_ == 0)
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_nat_dec_lt(v_start_2666_, v___x_2674_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2671_);
return v___x_2677_;
}
else
{
size_t v___x_2678_; size_t v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_usize_of_nat(v_start_2666_);
v___x_2679_ = lean_usize_of_nat(v___x_2674_);
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2662_, v_groupByFilename_2663_, v_verbose_2664_, v_as_2665_, v___x_2678_, v___x_2679_, v___x_2671_, v___y_2668_, v___y_2669_);
return v___x_2680_;
}
}
else
{
size_t v___x_2681_; size_t v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_usize_of_nat(v_start_2666_);
v___x_2682_ = lean_usize_of_nat(v_stop_2667_);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2662_, v_groupByFilename_2663_, v_verbose_2664_, v_as_2665_, v___x_2681_, v___x_2682_, v___x_2671_, v___y_2668_, v___y_2669_);
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object* v_useErrorFormat_2684_, lean_object* v_groupByFilename_2685_, lean_object* v_verbose_2686_, lean_object* v_as_2687_, lean_object* v_start_2688_, lean_object* v_stop_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
uint8_t v_useErrorFormat_boxed_2693_; uint8_t v_groupByFilename_boxed_2694_; uint8_t v_verbose_boxed_2695_; lean_object* v_res_2696_; 
v_useErrorFormat_boxed_2693_ = lean_unbox(v_useErrorFormat_2684_);
v_groupByFilename_boxed_2694_ = lean_unbox(v_groupByFilename_2685_);
v_verbose_boxed_2695_ = lean_unbox(v_verbose_2686_);
v_res_2696_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_boxed_2693_, v_groupByFilename_boxed_2694_, v_verbose_boxed_2695_, v_as_2687_, v_start_2688_, v_stop_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v_stop_2689_);
lean_dec(v_start_2688_);
lean_dec_ref(v_as_2687_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object* v_as_2697_, size_t v_i_2698_, size_t v_stop_2699_, lean_object* v_b_2700_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_usize_dec_eq(v_i_2698_, v_stop_2699_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; 
v___x_2702_ = lean_array_uget_borrowed(v_as_2697_, v_i_2698_);
v___x_2703_ = lean_nat_add(v_b_2700_, v___x_2702_);
lean_dec(v_b_2700_);
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_add(v_i_2698_, v___x_2704_);
v_i_2698_ = v___x_2705_;
v_b_2700_ = v___x_2703_;
goto _start;
}
else
{
return v_b_2700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object* v_as_2707_, lean_object* v_i_2708_, lean_object* v_stop_2709_, lean_object* v_b_2710_){
_start:
{
size_t v_i_boxed_2711_; size_t v_stop_boxed_2712_; lean_object* v_res_2713_; 
v_i_boxed_2711_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_stop_boxed_2712_ = lean_unbox_usize(v_stop_2709_);
lean_dec(v_stop_2709_);
v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v_as_2707_, v_i_boxed_2711_, v_stop_boxed_2712_, v_b_2710_);
lean_dec_ref(v_as_2707_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object* v_as_2714_, size_t v_i_2715_, size_t v_stop_2716_, lean_object* v_b_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_usize_dec_eq(v_i_2715_, v_stop_2716_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_array_uget_borrowed(v_as_2714_, v_i_2715_);
lean_inc(v___x_2721_);
v___x_2722_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v___x_2721_, v___y_2718_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v_a_2725_; uint8_t v___x_2729_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2729_ = lean_unbox(v_a_2723_);
lean_dec(v_a_2723_);
if (v___x_2729_ == 0)
{
v_a_2725_ = v_b_2717_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2730_; 
lean_inc(v___x_2721_);
v___x_2730_ = lean_array_push(v_b_2717_, v___x_2721_);
v_a_2725_ = v___x_2730_;
goto v___jp_2724_;
}
v___jp_2724_:
{
size_t v___x_2726_; size_t v___x_2727_; 
v___x_2726_ = ((size_t)1ULL);
v___x_2727_ = lean_usize_add(v_i_2715_, v___x_2726_);
v_i_2715_ = v___x_2727_;
v_b_2717_ = v_a_2725_;
goto _start;
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec_ref(v_b_2717_);
v_a_2731_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2722_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2722_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_b_2717_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object* v_as_2740_, lean_object* v_i_2741_, lean_object* v_stop_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
size_t v_i_boxed_2746_; size_t v_stop_boxed_2747_; lean_object* v_res_2748_; 
v_i_boxed_2746_ = lean_unbox_usize(v_i_2741_);
lean_dec(v_i_2741_);
v_stop_boxed_2747_ = lean_unbox_usize(v_stop_2742_);
lean_dec(v_stop_2742_);
v_res_2748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2740_, v_i_boxed_2746_, v_stop_boxed_2747_, v_b_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v_as_2740_);
return v_res_2748_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__0));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__2));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__4));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__6));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__8));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__10));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__12));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object* v_results_2771_, lean_object* v_decls_2772_, uint8_t v_groupByFilename_2773_, lean_object* v_whereDesc_2774_, uint8_t v_verbose_2775_, lean_object* v_numLinters_2776_, uint8_t v_useErrorFormat_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = lean_array_get_size(v_results_2771_);
v___x_2783_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_2777_, v_groupByFilename_2773_, v_verbose_2775_, v_results_2771_, v___x_2781_, v___x_2782_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2875_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2875_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2875_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v_a_2843_; lean_object* v___y_2856_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2788_ = lean_array_to_list(v_a_2784_);
v___x_2789_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2790_ = l_Lean_MessageData_joinSep(v___x_2788_, v___x_2789_);
v___x_2791_ = lean_array_get_size(v_decls_2772_);
v___x_2866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_2867_ = lean_nat_dec_lt(v___x_2781_, v___x_2791_);
if (v___x_2867_ == 0)
{
v_a_2843_ = v___x_2866_;
goto v___jp_2842_;
}
else
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_nat_dec_le(v___x_2791_, v___x_2791_);
if (v___x_2868_ == 0)
{
if (v___x_2867_ == 0)
{
v_a_2843_ = v___x_2866_;
goto v___jp_2842_;
}
else
{
size_t v___x_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v___x_2869_ = ((size_t)0ULL);
v___x_2870_ = lean_usize_of_nat(v___x_2791_);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2772_, v___x_2869_, v___x_2870_, v___x_2866_, v_a_2779_);
v___y_2856_ = v___x_2871_;
goto v___jp_2855_;
}
}
else
{
size_t v___x_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = ((size_t)0ULL);
v___x_2873_ = lean_usize_of_nat(v___x_2791_);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2772_, v___x_2872_, v___x_2873_, v___x_2866_, v_a_2779_);
v___y_2856_ = v___x_2874_;
goto v___jp_2855_;
}
}
v___jp_2792_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_inc_ref(v___y_2795_);
v___x_2796_ = l_Lean_stringToMessageData(v___y_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___y_2793_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__1, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_nat_sub(v___x_2791_, v___y_2794_);
v___x_2801_ = l_Nat_reprFast(v___x_2800_);
v___x_2802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
v___x_2803_ = l_Lean_MessageData_ofFormat(v___x_2802_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2799_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__3, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = l_Nat_reprFast(v___y_2794_);
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = l_Lean_MessageData_ofFormat(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2806_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__5, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Lean_stringToMessageData(v_whereDesc_2774_);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__7, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7);
v___x_2816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = l_Nat_reprFast(v_numLinters_2776_);
v___x_2818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
v___x_2819_ = l_Lean_MessageData_ofFormat(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2816_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__9, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2790_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2823_);
v___x_2825_ = v___x_2786_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
v___jp_2827_:
{
if (v_verbose_2775_ == 0)
{
lean_object* v___x_2830_; 
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_del_object(v___x_2786_);
lean_dec(v_numLinters_2776_);
lean_dec_ref(v_whereDesc_2774_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2790_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2831_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__11, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11);
lean_inc(v___y_2829_);
v___x_2832_ = l_Nat_reprFast(v___y_2829_);
v___x_2833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
v___x_2834_ = l_Lean_MessageData_ofFormat(v___x_2833_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2831_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__13, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = lean_nat_dec_eq(v___y_2829_, v___x_2838_);
lean_dec(v___y_2829_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; 
v___x_2840_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__14));
v___y_2793_ = v___x_2837_;
v___y_2794_ = v___y_2828_;
v___y_2795_ = v___x_2840_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2841_; 
v___x_2841_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___y_2793_ = v___x_2837_;
v___y_2794_ = v___y_2828_;
v___y_2795_ = v___x_2841_;
goto v___jp_2792_;
}
}
}
v___jp_2842_:
{
lean_object* v___x_2844_; size_t v_sz_2845_; size_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2844_ = lean_array_get_size(v_a_2843_);
lean_dec_ref(v_a_2843_);
v_sz_2845_ = lean_array_size(v_results_2771_);
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_2845_, v___x_2846_, v_results_2771_);
v___x_2848_ = lean_array_get_size(v___x_2847_);
v___x_2849_ = lean_nat_dec_lt(v___x_2781_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_dec_ref(v___x_2847_);
v___y_2828_ = v___x_2844_;
v___y_2829_ = v___x_2781_;
goto v___jp_2827_;
}
else
{
uint8_t v___x_2850_; 
v___x_2850_ = lean_nat_dec_le(v___x_2848_, v___x_2848_);
if (v___x_2850_ == 0)
{
if (v___x_2849_ == 0)
{
lean_dec_ref(v___x_2847_);
v___y_2828_ = v___x_2844_;
v___y_2829_ = v___x_2781_;
goto v___jp_2827_;
}
else
{
size_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_usize_of_nat(v___x_2848_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_2847_, v___x_2846_, v___x_2851_, v___x_2781_);
lean_dec_ref(v___x_2847_);
v___y_2828_ = v___x_2844_;
v___y_2829_ = v___x_2852_;
goto v___jp_2827_;
}
}
else
{
size_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_usize_of_nat(v___x_2848_);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_2847_, v___x_2846_, v___x_2853_, v___x_2781_);
lean_dec_ref(v___x_2847_);
v___y_2828_ = v___x_2844_;
v___y_2829_ = v___x_2854_;
goto v___jp_2827_;
}
}
}
v___jp_2855_:
{
if (lean_obj_tag(v___y_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___y_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___y_2856_, 1);
v_a_2843_ = v_a_2857_;
goto v___jp_2842_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v___x_2790_);
lean_del_object(v___x_2786_);
lean_dec(v_numLinters_2776_);
lean_dec_ref(v_whereDesc_2774_);
lean_dec_ref(v_results_2771_);
v_a_2858_ = lean_ctor_get(v___y_2856_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___y_2856_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___y_2856_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___y_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_numLinters_2776_);
lean_dec_ref(v_whereDesc_2774_);
lean_dec_ref(v_results_2771_);
v_a_2876_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2783_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2783_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object* v_results_2884_, lean_object* v_decls_2885_, lean_object* v_groupByFilename_2886_, lean_object* v_whereDesc_2887_, lean_object* v_verbose_2888_, lean_object* v_numLinters_2889_, lean_object* v_useErrorFormat_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
uint8_t v_groupByFilename_boxed_2894_; uint8_t v_verbose_boxed_2895_; uint8_t v_useErrorFormat_boxed_2896_; lean_object* v_res_2897_; 
v_groupByFilename_boxed_2894_ = lean_unbox(v_groupByFilename_2886_);
v_verbose_boxed_2895_ = lean_unbox(v_verbose_2888_);
v_useErrorFormat_boxed_2896_ = lean_unbox(v_useErrorFormat_2890_);
v_res_2897_ = l_Lean_Linter_EnvLinter_formatLinterResults(v_results_2884_, v_decls_2885_, v_groupByFilename_boxed_2894_, v_whereDesc_2887_, v_verbose_boxed_2895_, v_numLinters_2889_, v_useErrorFormat_boxed_2896_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec_ref(v_decls_2885_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object* v_as_2898_, size_t v_i_2899_, size_t v_stop_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2898_, v_i_2899_, v_stop_2900_, v_b_2901_, v___y_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object* v_as_2906_, lean_object* v_i_2907_, lean_object* v_stop_2908_, lean_object* v_b_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
size_t v_i_boxed_2913_; size_t v_stop_boxed_2914_; lean_object* v_res_2915_; 
v_i_boxed_2913_ = lean_unbox_usize(v_i_2907_);
lean_dec(v_i_2907_);
v_stop_boxed_2914_ = lean_unbox_usize(v_stop_2908_);
lean_dec(v_stop_2908_);
v_res_2915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(v_as_2906_, v_i_boxed_2913_, v_stop_boxed_2914_, v_b_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v_as_2906_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object* v_r_2916_, lean_object* v_k_2917_, lean_object* v_x_2918_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_array_push(v_r_2916_, v_k_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object* v_r_2920_, lean_object* v_k_2921_, lean_object* v_x_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(v_r_2920_, v_k_2921_, v_x_2922_);
lean_dec_ref(v_x_2922_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object* v_f_2924_, lean_object* v_x1_2925_, lean_object* v_x2_2926_, lean_object* v_x3_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_apply_3(v_f_2924_, v_x1_2925_, v_x2_2926_, v_x3_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2929_, lean_object* v_keys_2930_, lean_object* v_vals_2931_, lean_object* v_i_2932_, lean_object* v_acc_2933_){
_start:
{
lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = lean_array_get_size(v_keys_2930_);
v___x_2935_ = lean_nat_dec_lt(v_i_2932_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_dec(v_i_2932_);
lean_dec(v_f_2929_);
return v_acc_2933_;
}
else
{
lean_object* v_k_2936_; lean_object* v_v_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_k_2936_ = lean_array_fget_borrowed(v_keys_2930_, v_i_2932_);
v_v_2937_ = lean_array_fget_borrowed(v_vals_2931_, v_i_2932_);
lean_inc(v_f_2929_);
lean_inc(v_v_2937_);
lean_inc(v_k_2936_);
v___x_2938_ = lean_apply_3(v_f_2929_, v_acc_2933_, v_k_2936_, v_v_2937_);
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2940_ = lean_nat_add(v_i_2932_, v___x_2939_);
lean_dec(v_i_2932_);
v_i_2932_ = v___x_2940_;
v_acc_2933_ = v___x_2938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2942_, lean_object* v_keys_2943_, lean_object* v_vals_2944_, lean_object* v_i_2945_, lean_object* v_acc_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2942_, v_keys_2943_, v_vals_2944_, v_i_2945_, v_acc_2946_);
lean_dec_ref(v_vals_2944_);
lean_dec_ref(v_keys_2943_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2948_, lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
if (lean_obj_tag(v_x_2949_) == 0)
{
lean_object* v_es_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_es_2951_ = lean_ctor_get(v_x_2949_, 0);
v___x_2952_ = lean_unsigned_to_nat(0u);
v___x_2953_ = lean_array_get_size(v_es_2951_);
v___x_2954_ = lean_nat_dec_lt(v___x_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v_f_2948_);
return v_x_2950_;
}
else
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_nat_dec_le(v___x_2953_, v___x_2953_);
if (v___x_2955_ == 0)
{
if (v___x_2954_ == 0)
{
lean_dec(v_f_2948_);
return v_x_2950_;
}
else
{
size_t v___x_2956_; size_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = lean_usize_of_nat(v___x_2953_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2948_, v_es_2951_, v___x_2956_, v___x_2957_, v_x_2950_);
return v___x_2958_;
}
}
else
{
size_t v___x_2959_; size_t v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = lean_usize_of_nat(v___x_2953_);
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2948_, v_es_2951_, v___x_2959_, v___x_2960_, v_x_2950_);
return v___x_2961_;
}
}
}
else
{
lean_object* v_ks_2962_; lean_object* v_vs_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_ks_2962_ = lean_ctor_get(v_x_2949_, 0);
v_vs_2963_ = lean_ctor_get(v_x_2949_, 1);
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2948_, v_ks_2962_, v_vs_2963_, v___x_2964_, v_x_2950_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2966_, lean_object* v_as_2967_, size_t v_i_2968_, size_t v_stop_2969_, lean_object* v_b_2970_){
_start:
{
lean_object* v___y_2972_; uint8_t v___x_2976_; 
v___x_2976_ = lean_usize_dec_eq(v_i_2968_, v_stop_2969_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_array_uget_borrowed(v_as_2967_, v_i_2968_);
switch(lean_obj_tag(v___x_2977_))
{
case 0:
{
lean_object* v_key_2978_; lean_object* v_val_2979_; lean_object* v___x_2980_; 
v_key_2978_ = lean_ctor_get(v___x_2977_, 0);
v_val_2979_ = lean_ctor_get(v___x_2977_, 1);
lean_inc(v_f_2966_);
lean_inc(v_val_2979_);
lean_inc(v_key_2978_);
v___x_2980_ = lean_apply_3(v_f_2966_, v_b_2970_, v_key_2978_, v_val_2979_);
v___y_2972_ = v___x_2980_;
goto v___jp_2971_;
}
case 1:
{
lean_object* v_node_2981_; lean_object* v___x_2982_; 
v_node_2981_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_f_2966_);
v___x_2982_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_2966_, v_node_2981_, v_b_2970_);
v___y_2972_ = v___x_2982_;
goto v___jp_2971_;
}
default: 
{
v___y_2972_ = v_b_2970_;
goto v___jp_2971_;
}
}
}
else
{
lean_dec(v_f_2966_);
return v_b_2970_;
}
v___jp_2971_:
{
size_t v___x_2973_; size_t v___x_2974_; 
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_add(v_i_2968_, v___x_2973_);
v_i_2968_ = v___x_2974_;
v_b_2970_ = v___y_2972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2983_, lean_object* v_as_2984_, lean_object* v_i_2985_, lean_object* v_stop_2986_, lean_object* v_b_2987_){
_start:
{
size_t v_i_boxed_2988_; size_t v_stop_boxed_2989_; lean_object* v_res_2990_; 
v_i_boxed_2988_ = lean_unbox_usize(v_i_2985_);
lean_dec(v_i_2985_);
v_stop_boxed_2989_ = lean_unbox_usize(v_stop_2986_);
lean_dec(v_stop_2986_);
v_res_2990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2983_, v_as_2984_, v_i_boxed_2988_, v_stop_boxed_2989_, v_b_2987_);
lean_dec_ref(v_as_2984_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_2991_, v_x_2992_, v_x_2993_);
lean_dec_ref(v_x_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object* v_map_2995_, lean_object* v_f_2996_, lean_object* v_init_2997_){
_start:
{
lean_object* v___f_2998_; lean_object* v___x_2999_; 
v___f_2998_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2998_, 0, v_f_2996_);
v___x_2999_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v___f_2998_, v_map_2995_, v_init_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object* v_map_3000_, lean_object* v_f_3001_, lean_object* v_init_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3000_, v_f_3001_, v_init_3002_);
lean_dec_ref(v_map_3000_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3007_; lean_object* v_env_3008_; lean_object* v___x_3009_; lean_object* v_map_u2082_3010_; lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3007_ = lean_st_ref_get(v_a_3005_);
v_env_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_ref(v_env_3008_);
lean_dec(v___x_3007_);
v___x_3009_ = l_Lean_Environment_constants(v_env_3008_);
v_map_u2082_3010_ = lean_ctor_get(v___x_3009_, 1);
lean_inc_ref(v_map_u2082_3010_);
lean_dec_ref(v___x_3009_);
v___f_3011_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0));
v___x_3012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_3013_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_u2082_3010_, v___f_3011_, v___x_3012_);
lean_dec_ref(v_map_u2082_3010_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3015_);
lean_dec(v_a_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule(v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object* v_00_u03c3_3026_, lean_object* v_00_u03b2_3027_, lean_object* v_map_3028_, lean_object* v_f_3029_, lean_object* v_init_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3028_, v_f_3029_, v_init_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object* v_00_u03c3_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_map_3034_, lean_object* v_f_3035_, lean_object* v_init_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(v_00_u03c3_3032_, v_00_u03b2_3033_, v_map_3034_, v_f_3035_, v_init_3036_);
lean_dec_ref(v_map_3034_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object* v_map_3038_, lean_object* v_f_3039_, lean_object* v_init_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3039_, v_map_3038_, v_init_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object* v_map_3042_, lean_object* v_f_3043_, lean_object* v_init_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(v_map_3042_, v_f_3043_, v_init_3044_);
lean_dec_ref(v_map_3042_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object* v_00_u03c3_3046_, lean_object* v_00_u03b2_3047_, lean_object* v_map_3048_, lean_object* v_f_3049_, lean_object* v_init_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3049_, v_map_3048_, v_init_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3052_, lean_object* v_00_u03b2_3053_, lean_object* v_map_3054_, lean_object* v_f_3055_, lean_object* v_init_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(v_00_u03c3_3052_, v_00_u03b2_3053_, v_map_3054_, v_f_3055_, v_init_3056_);
lean_dec_ref(v_map_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3058_, lean_object* v_00_u03b1_3059_, lean_object* v_00_u03b2_3060_, lean_object* v_f_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3061_, v_x_3062_, v_x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3065_, lean_object* v_00_u03b1_3066_, lean_object* v_00_u03b2_3067_, lean_object* v_f_3068_, lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(v_00_u03c3_3065_, v_00_u03b1_3066_, v_00_u03b2_3067_, v_f_3068_, v_x_3069_, v_x_3070_);
lean_dec_ref(v_x_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3072_, lean_object* v_00_u03b2_3073_, lean_object* v_00_u03c3_3074_, lean_object* v_f_3075_, lean_object* v_as_3076_, size_t v_i_3077_, size_t v_stop_3078_, lean_object* v_b_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3075_, v_as_3076_, v_i_3077_, v_stop_3078_, v_b_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3081_, lean_object* v_00_u03b2_3082_, lean_object* v_00_u03c3_3083_, lean_object* v_f_3084_, lean_object* v_as_3085_, lean_object* v_i_3086_, lean_object* v_stop_3087_, lean_object* v_b_3088_){
_start:
{
size_t v_i_boxed_3089_; size_t v_stop_boxed_3090_; lean_object* v_res_3091_; 
v_i_boxed_3089_ = lean_unbox_usize(v_i_3086_);
lean_dec(v_i_3086_);
v_stop_boxed_3090_ = lean_unbox_usize(v_stop_3087_);
lean_dec(v_stop_3087_);
v_res_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3081_, v_00_u03b2_3082_, v_00_u03c3_3083_, v_f_3084_, v_as_3085_, v_i_boxed_3089_, v_stop_boxed_3090_, v_b_3088_);
lean_dec_ref(v_as_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3092_, lean_object* v_00_u03b1_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_f_3095_, lean_object* v_keys_3096_, lean_object* v_vals_3097_, lean_object* v_heq_3098_, lean_object* v_i_3099_, lean_object* v_acc_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3095_, v_keys_3096_, v_vals_3097_, v_i_3099_, v_acc_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3102_, lean_object* v_00_u03b1_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_f_3105_, lean_object* v_keys_3106_, lean_object* v_vals_3107_, lean_object* v_heq_3108_, lean_object* v_i_3109_, lean_object* v_acc_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3102_, v_00_u03b1_3103_, v_00_u03b2_3104_, v_f_3105_, v_keys_3106_, v_vals_3107_, v_heq_3108_, v_i_3109_, v_acc_3110_);
lean_dec_ref(v_vals_3107_);
lean_dec_ref(v_keys_3106_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object* v_x_3112_, lean_object* v_x_3113_){
_start:
{
if (lean_obj_tag(v_x_3113_) == 0)
{
return v_x_3112_;
}
else
{
lean_object* v_key_3114_; lean_object* v_tail_3115_; lean_object* v___x_3116_; 
v_key_3114_ = lean_ctor_get(v_x_3113_, 0);
lean_inc(v_key_3114_);
v_tail_3115_ = lean_ctor_get(v_x_3113_, 2);
lean_inc(v_tail_3115_);
lean_dec_ref_known(v_x_3113_, 3);
v___x_3116_ = lean_array_push(v_x_3112_, v_key_3114_);
v_x_3112_ = v___x_3116_;
v_x_3113_ = v_tail_3115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object* v_as_3118_, size_t v_i_3119_, size_t v_stop_3120_, lean_object* v_b_3121_){
_start:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_usize_dec_eq(v_i_3119_, v_stop_3120_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; size_t v___x_3125_; size_t v___x_3126_; 
v___x_3123_ = lean_array_uget_borrowed(v_as_3118_, v_i_3119_);
lean_inc(v___x_3123_);
v___x_3124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(v_b_3121_, v___x_3123_);
v___x_3125_ = ((size_t)1ULL);
v___x_3126_ = lean_usize_add(v_i_3119_, v___x_3125_);
v_i_3119_ = v___x_3126_;
v_b_3121_ = v___x_3124_;
goto _start;
}
else
{
return v_b_3121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object* v_as_3128_, lean_object* v_i_3129_, lean_object* v_stop_3130_, lean_object* v_b_3131_){
_start:
{
size_t v_i_boxed_3132_; size_t v_stop_boxed_3133_; lean_object* v_res_3134_; 
v_i_boxed_3132_ = lean_unbox_usize(v_i_3129_);
lean_dec(v_i_3129_);
v_stop_boxed_3133_ = lean_unbox_usize(v_stop_3130_);
lean_dec(v_stop_3130_);
v_res_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_as_3128_, v_i_boxed_3132_, v_stop_boxed_3133_, v_b_3131_);
lean_dec_ref(v_as_3128_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v_a_3139_; lean_object* v_env_3140_; lean_object* v___x_3141_; lean_object* v_map_u2081_3142_; lean_object* v_buckets_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3137_ = lean_st_ref_get(v_a_3135_);
v___x_3138_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3135_);
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
v_env_3140_ = lean_ctor_get(v___x_3137_, 0);
lean_inc_ref(v_env_3140_);
lean_dec(v___x_3137_);
v___x_3141_ = l_Lean_Environment_constants(v_env_3140_);
v_map_u2081_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_ref(v_map_u2081_3142_);
lean_dec_ref(v___x_3141_);
v_buckets_3143_ = lean_ctor_get(v_map_u2081_3142_, 1);
lean_inc_ref(v_buckets_3143_);
lean_dec_ref(v_map_u2081_3142_);
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = lean_array_get_size(v_buckets_3143_);
v___x_3146_ = lean_nat_dec_lt(v___x_3144_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_dec_ref(v_buckets_3143_);
lean_dec(v_a_3139_);
return v___x_3138_;
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_nat_dec_le(v___x_3145_, v___x_3145_);
if (v___x_3147_ == 0)
{
if (v___x_3146_ == 0)
{
lean_dec_ref(v_buckets_3143_);
lean_dec(v_a_3139_);
return v___x_3138_;
}
else
{
lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3157_; 
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3138_, 0);
lean_dec(v_unused_3158_);
v___x_3149_ = v___x_3138_;
v_isShared_3150_ = v_isSharedCheck_3157_;
goto v_resetjp_3148_;
}
else
{
lean_dec(v___x_3138_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3157_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
size_t v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3151_ = ((size_t)0ULL);
v___x_3152_ = lean_usize_of_nat(v___x_3145_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3143_, v___x_3151_, v___x_3152_, v_a_3139_);
lean_dec_ref(v_buckets_3143_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3153_);
v___x_3155_ = v___x_3149_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3168_; 
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_3138_, 0);
lean_dec(v_unused_3169_);
v___x_3160_ = v___x_3138_;
v_isShared_3161_ = v_isSharedCheck_3168_;
goto v_resetjp_3159_;
}
else
{
lean_dec(v___x_3138_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3168_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = lean_usize_of_nat(v___x_3145_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3143_, v___x_3162_, v___x_3163_, v_a_3139_);
lean_dec_ref(v_buckets_3143_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3164_);
v___x_3166_ = v___x_3160_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3170_);
lean_dec(v_a_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_Linter_EnvLinter_getAllDecls(v_a_3177_, v_a_3178_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object* v_msg_3181_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_panic_fn_borrowed(v___x_3182_, v_msg_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3187_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2));
v___x_3188_ = lean_unsigned_to_nat(14u);
v___x_3189_ = lean_unsigned_to_nat(22u);
v___x_3190_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1));
v___x_3191_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0));
v___x_3192_ = l_mkPanicMessageWithDecl(v___x_3191_, v___x_3190_, v___x_3189_, v___x_3188_, v___x_3187_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object* v___x_3193_, lean_object* v___x_3194_, lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_dec_ref(v___x_3194_);
return v_x_3195_;
}
else
{
lean_object* v_key_3197_; lean_object* v_tail_3198_; uint8_t v___x_3199_; lean_object* v___y_3201_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_key_3197_ = lean_ctor_get(v_x_3196_, 0);
lean_inc(v_key_3197_);
v_tail_3198_ = lean_ctor_get(v_x_3196_, 2);
lean_inc(v_tail_3198_);
lean_dec_ref_known(v_x_3196_, 3);
v___x_3199_ = 0;
lean_inc_ref(v___x_3194_);
v___x_3208_ = l_Lean_Environment_const2ModIdx(v___x_3194_);
v___x_3209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v___x_3208_, v_key_3197_);
lean_dec_ref(v___x_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3);
v___x_3211_ = l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(v___x_3210_);
v___y_3201_ = v___x_3211_;
goto v___jp_3200_;
}
else
{
lean_object* v_val_3212_; 
v_val_3212_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_val_3212_);
lean_dec_ref_known(v___x_3209_, 1);
v___y_3201_ = v_val_3212_;
goto v___jp_3200_;
}
v___jp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3202_ = lean_box(v___x_3199_);
v___x_3203_ = lean_array_get(v___x_3202_, v___x_3193_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec(v___x_3202_);
v___x_3204_ = lean_unbox(v___x_3203_);
lean_dec(v___x_3203_);
if (v___x_3204_ == 0)
{
lean_dec(v_key_3197_);
v_x_3196_ = v_tail_3198_;
goto _start;
}
else
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_array_push(v_x_3195_, v_key_3197_);
v_x_3195_ = v___x_3206_;
v_x_3196_ = v_tail_3198_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3213_, v___x_3214_, v_x_3215_, v_x_3216_);
lean_dec_ref(v___x_3213_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object* v___x_3218_, lean_object* v___x_3219_, lean_object* v_as_3220_, size_t v_i_3221_, size_t v_stop_3222_, lean_object* v_b_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_usize_dec_eq(v_i_3221_, v_stop_3222_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; size_t v___x_3227_; size_t v___x_3228_; 
v___x_3225_ = lean_array_uget_borrowed(v_as_3220_, v_i_3221_);
lean_inc(v___x_3225_);
lean_inc_ref(v___x_3219_);
v___x_3226_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3218_, v___x_3219_, v_b_3223_, v___x_3225_);
v___x_3227_ = ((size_t)1ULL);
v___x_3228_ = lean_usize_add(v_i_3221_, v___x_3227_);
v_i_3221_ = v___x_3228_;
v_b_3223_ = v___x_3226_;
goto _start;
}
else
{
lean_dec_ref(v___x_3219_);
return v_b_3223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object* v___x_3230_, lean_object* v___x_3231_, lean_object* v_as_3232_, lean_object* v_i_3233_, lean_object* v_stop_3234_, lean_object* v_b_3235_){
_start:
{
size_t v_i_boxed_3236_; size_t v_stop_boxed_3237_; lean_object* v_res_3238_; 
v_i_boxed_3236_ = lean_unbox_usize(v_i_3233_);
lean_dec(v_i_3233_);
v_stop_boxed_3237_ = lean_unbox_usize(v_stop_3234_);
lean_dec(v_stop_3234_);
v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3230_, v___x_3231_, v_as_3232_, v_i_boxed_3236_, v_stop_boxed_3237_, v_b_3235_);
lean_dec_ref(v_as_3232_);
lean_dec_ref(v___x_3230_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object* v_pkg_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_bs_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3243_ == 0)
{
return v_bs_3242_;
}
else
{
lean_object* v_v_3244_; lean_object* v___x_3245_; lean_object* v_bs_x27_3246_; uint8_t v___x_3247_; size_t v___x_3248_; size_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_v_3244_ = lean_array_uget(v_bs_3242_, v_i_3241_);
v___x_3245_ = lean_unsigned_to_nat(0u);
v_bs_x27_3246_ = lean_array_uset(v_bs_3242_, v_i_3241_, v___x_3245_);
v___x_3247_ = l_Lean_Name_isPrefixOf(v_pkg_3239_, v_v_3244_);
lean_dec(v_v_3244_);
v___x_3248_ = ((size_t)1ULL);
v___x_3249_ = lean_usize_add(v_i_3241_, v___x_3248_);
v___x_3250_ = lean_box(v___x_3247_);
v___x_3251_ = lean_array_uset(v_bs_x27_3246_, v_i_3241_, v___x_3250_);
v_i_3241_ = v___x_3249_;
v_bs_3242_ = v___x_3251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object* v_pkg_3253_, lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_bs_3256_){
_start:
{
size_t v_sz_boxed_3257_; size_t v_i_boxed_3258_; lean_object* v_res_3259_; 
v_sz_boxed_3257_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3258_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3253_, v_sz_boxed_3257_, v_i_boxed_3258_, v_bs_3256_);
lean_dec(v_pkg_3253_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object* v_pkg_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v_a_3265_; lean_object* v_env_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_map_u2081_3269_; lean_object* v_buckets_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3263_ = lean_st_ref_get(v_a_3261_);
v___x_3264_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3261_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
v_env_3266_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref_n(v_env_3266_, 2);
lean_dec(v___x_3263_);
v___x_3267_ = l_Lean_Environment_header(v_env_3266_);
v___x_3268_ = l_Lean_Environment_constants(v_env_3266_);
v_map_u2081_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc_ref(v_map_u2081_3269_);
lean_dec_ref(v___x_3268_);
v_buckets_3270_ = lean_ctor_get(v_map_u2081_3269_, 1);
lean_inc_ref(v_buckets_3270_);
lean_dec_ref(v_map_u2081_3269_);
v___x_3271_ = lean_unsigned_to_nat(0u);
v___x_3272_ = lean_array_get_size(v_buckets_3270_);
v___x_3273_ = lean_nat_dec_lt(v___x_3271_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_dec_ref(v_buckets_3270_);
lean_dec_ref(v___x_3267_);
lean_dec_ref(v_env_3266_);
lean_dec(v_a_3265_);
return v___x_3264_;
}
else
{
lean_object* v___x_3274_; size_t v_sz_3275_; size_t v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3274_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3267_);
v_sz_3275_ = lean_array_size(v___x_3274_);
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3260_, v_sz_3275_, v___x_3276_, v___x_3274_);
v___x_3278_ = lean_nat_dec_le(v___x_3272_, v___x_3272_);
if (v___x_3278_ == 0)
{
if (v___x_3273_ == 0)
{
lean_dec_ref(v___x_3277_);
lean_dec_ref(v_buckets_3270_);
lean_dec_ref(v_env_3266_);
lean_dec(v_a_3265_);
return v___x_3264_;
}
else
{
lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3287_; 
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3264_, 0);
lean_dec(v_unused_3288_);
v___x_3280_ = v___x_3264_;
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
else
{
lean_dec(v___x_3264_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
size_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3282_ = lean_usize_of_nat(v___x_3272_);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3277_, v_env_3266_, v_buckets_3270_, v___x_3276_, v___x_3282_, v_a_3265_);
lean_dec_ref(v_buckets_3270_);
lean_dec_ref(v___x_3277_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3283_);
v___x_3285_ = v___x_3280_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3297_; 
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3264_, 0);
lean_dec(v_unused_3298_);
v___x_3290_ = v___x_3264_;
v_isShared_3291_ = v_isSharedCheck_3297_;
goto v_resetjp_3289_;
}
else
{
lean_dec(v___x_3264_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3297_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
size_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3292_ = lean_usize_of_nat(v___x_3272_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3277_, v_env_3266_, v_buckets_3270_, v___x_3276_, v___x_3292_, v_a_3265_);
lean_dec_ref(v_buckets_3270_);
lean_dec_ref(v___x_3277_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3293_);
v___x_3295_ = v___x_3290_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object* v_pkg_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec(v_pkg_3299_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object* v_pkg_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3303_, v_a_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object* v_pkg_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Linter_EnvLinter_getDeclsInPackage(v_pkg_3308_, v_a_3309_, v_a_3310_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_pkg_3308_);
return v_res_3312_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_EnvLinter_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default = _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default();
l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity = _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_EnvLinter_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_EnvLinter_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_EnvLinter_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_EnvLinter_Frontend(builtin);
}
#ifdef __cplusplus
}
#endif

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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v___x_189_, v_k_185_);
v___x_192_ = lean_bool_not(v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_sub(v___x_186_, v___x_193_);
v___x_195_ = lean_array_fget_borrowed(v_as_184_, v___x_194_);
v___x_196_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v___x_195_, v_k_185_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___lam__0(v_k_185_, v___x_195_);
v___x_198_ = lean_bool_not(v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(v_a_183_, v_as_184_, v_k_185_, v___x_187_, v___x_194_);
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = lean_nat_dec_lt(v___x_194_, v___x_186_);
if (v___x_200_ == 0)
{
lean_dec(v___x_194_);
lean_dec_ref(v_a_183_);
return v_as_184_;
}
else
{
lean_object* v___x_201_; lean_object* v_xs_x27_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
v_xs_x27_202_ = lean_array_fset(v_as_184_, v___x_194_, v___x_201_);
v___x_203_ = lean_array_fset(v_xs_x27_202_, v___x_194_, v_a_183_);
lean_dec(v___x_194_);
return v___x_203_;
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec(v___x_194_);
v___x_204_ = lean_array_push(v_as_184_, v_a_183_);
return v___x_204_;
}
}
else
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_lt(v___x_187_, v___x_186_);
if (v___x_205_ == 0)
{
lean_dec_ref(v_a_183_);
return v_as_184_;
}
else
{
lean_object* v___x_206_; lean_object* v_xs_x27_207_; lean_object* v___x_208_; 
v___x_206_ = lean_box(0);
v_xs_x27_207_ = lean_array_fset(v_as_184_, v___x_187_, v___x_206_);
v___x_208_ = lean_array_fset(v_xs_x27_207_, v___x_187_, v_a_183_);
return v___x_208_;
}
}
}
else
{
lean_object* v_as_209_; lean_object* v___x_210_; 
v_as_209_ = lean_array_push(v_as_184_, v_a_183_);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_187_, v_as_209_, v___x_186_);
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_array_push(v_as_184_, v_a_183_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0___boxed(lean_object* v_a_212_, lean_object* v_as_213_, lean_object* v_k_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0(v_a_212_, v_as_213_, v_k_214_);
lean_dec_ref(v_k_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(lean_object* v_opts_x3f_216_, lean_object* v_init_217_, lean_object* v_x_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_d_223_; 
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v_k_226_; lean_object* v_v_227_; lean_object* v_l_228_; lean_object* v_r_229_; lean_object* v___x_230_; 
v_k_226_ = lean_ctor_get(v_x_218_, 1);
lean_inc(v_k_226_);
v_v_227_ = lean_ctor_get(v_x_218_, 2);
lean_inc(v_v_227_);
v_l_228_ = lean_ctor_get(v_x_218_, 3);
lean_inc(v_l_228_);
v_r_229_ = lean_ctor_get(v_x_218_, 4);
lean_inc(v_r_229_);
lean_dec_ref_known(v_x_218_, 5);
v___x_230_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(v_opts_x3f_216_, v_init_217_, v_l_228_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
if (lean_obj_tag(v_a_231_) == 0)
{
lean_object* v_a_232_; 
lean_dec_ref_known(v___x_230_, 1);
lean_dec(v_r_229_);
lean_dec(v_v_227_);
lean_dec(v_k_226_);
v_a_232_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v_a_231_, 1);
v_d_223_ = v_a_232_;
goto v___jp_222_;
}
else
{
lean_object* v_a_233_; 
v_a_233_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v_a_231_, 1);
if (lean_obj_tag(v_opts_x3f_216_) == 0)
{
lean_dec_ref_known(v___x_230_, 1);
goto v___jp_234_;
}
else
{
lean_object* v_val_247_; uint8_t v___x_248_; 
v_val_247_ = lean_ctor_get(v_opts_x3f_216_, 0);
v___x_248_ = l_Lean_Linter_isLinterEnabledByOptions(v_k_226_, v_val_247_);
if (v___x_248_ == 0)
{
lean_dec(v_a_233_);
lean_dec(v_v_227_);
lean_dec(v_k_226_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_230_, 1);
if (lean_obj_tag(v_a_249_) == 0)
{
lean_object* v_a_250_; 
lean_dec(v_r_229_);
v_a_250_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v_a_249_, 1);
v_d_223_ = v_a_250_;
goto v___jp_222_;
}
else
{
lean_object* v_a_251_; 
v_a_251_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v_a_249_, 1);
v_init_217_ = v_a_251_;
v_x_218_ = v_r_229_;
goto _start;
}
}
else
{
lean_dec(v_r_229_);
return v___x_230_;
}
}
else
{
lean_dec_ref_known(v___x_230_, 1);
goto v___jp_234_;
}
}
v___jp_234_:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_k_226_, v_v_227_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc_n(v_a_236_, 2);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0(v_a_236_, v_a_233_, v_a_236_);
lean_dec(v_a_236_);
v_init_217_ = v___x_237_;
v_x_218_ = v_r_229_;
goto _start;
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_a_233_);
lean_dec(v_r_229_);
v_a_239_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_235_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_235_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
else
{
lean_dec(v_r_229_);
lean_dec(v_v_227_);
lean_dec(v_k_226_);
return v___x_230_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_init_217_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v_d_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1___boxed(lean_object* v_opts_x3f_255_, lean_object* v_init_256_, lean_object* v_x_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(v_opts_x3f_255_, v_init_256_, v_x_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v_opts_x3f_255_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object* v_opts_x3f_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; lean_object* v_env_269_; lean_object* v___x_270_; lean_object* v_toEnvExtension_271_; lean_object* v_asyncMode_272_; lean_object* v___x_273_; lean_object* v_result_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_268_ = lean_st_ref_get(v_a_266_);
v_env_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref(v_env_269_);
lean_dec(v___x_268_);
v___x_270_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_271_ = lean_ctor_get(v___x_270_, 0);
v_asyncMode_272_ = lean_ctor_get(v_toEnvExtension_271_, 2);
v___x_273_ = lean_box(1);
v_result_274_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getEnvLinters___closed__0));
v___x_275_ = lean_box(0);
v___x_276_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_273_, v___x_270_, v_env_269_, v_asyncMode_272_, v___x_275_);
v___x_277_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__1(v_opts_x3f_264_, v_result_274_, v___x_276_, v_a_265_, v_a_266_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_a_282_; lean_object* v___x_284_; 
v_a_282_ = lean_ctor_get(v_a_278_, 0);
lean_inc(v_a_282_);
lean_dec(v_a_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v_a_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_277_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_277_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinters___boxed(lean_object* v_opts_x3f_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Linter_EnvLinter_getEnvLinters(v_opts_x3f_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_opts_x3f_295_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0(lean_object* v_a_300_, lean_object* v_as_301_, lean_object* v_k_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___redArg(v_a_300_, v_as_301_, v_k_302_, v_x_303_, v_x_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0___boxed(lean_object* v_a_308_, lean_object* v_as_309_, lean_object* v_k_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getEnvLinters_spec__0_spec__0(v_a_308_, v_as_309_, v_k_310_, v_x_311_, v_x_312_, v_x_313_, v_x_314_);
lean_dec_ref(v_k_310_);
return v_res_315_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_isLinterEnabledFor(lean_object* v_env_316_, lean_object* v_linter_317_, lean_object* v_decl_318_){
_start:
{
lean_object* v_optName_319_; lean_object* v___x_320_; 
v_optName_319_ = lean_ctor_get(v_linter_317_, 1);
v___x_320_ = l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(v_env_316_, v_decl_318_, v_optName_319_);
if (lean_obj_tag(v___x_320_) == 0)
{
uint8_t v___x_321_; 
v___x_321_ = 0;
return v___x_321_;
}
else
{
lean_object* v_val_322_; uint8_t v___x_323_; 
v_val_322_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v___x_320_, 1);
v___x_323_ = lean_unbox(v_val_322_);
lean_dec(v_val_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isLinterEnabledFor___boxed(lean_object* v_env_324_, lean_object* v_linter_325_, lean_object* v_decl_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lean_Linter_EnvLinter_isLinterEnabledFor(v_env_324_, v_linter_325_, v_decl_326_);
lean_dec_ref(v_linter_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object* v___x_329_, lean_object* v_linter_330_, lean_object* v_as_331_, size_t v_i_332_, size_t v_stop_333_, lean_object* v_b_334_){
_start:
{
lean_object* v___y_336_; uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_eq(v_i_332_, v_stop_333_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_array_uget_borrowed(v_as_331_, v_i_332_);
lean_inc(v___x_341_);
lean_inc_ref(v___x_329_);
v___x_342_ = l_Lean_Linter_EnvLinter_isLinterEnabledFor(v___x_329_, v_linter_330_, v___x_341_);
if (v___x_342_ == 0)
{
v___y_336_ = v_b_334_;
goto v___jp_335_;
}
else
{
lean_object* v___x_343_; 
lean_inc(v___x_341_);
v___x_343_ = lean_array_push(v_b_334_, v___x_341_);
v___y_336_ = v___x_343_;
goto v___jp_335_;
}
}
else
{
lean_dec_ref(v___x_329_);
return v_b_334_;
}
v___jp_335_:
{
size_t v___x_337_; size_t v___x_338_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_332_, v___x_337_);
v_i_332_ = v___x_338_;
v_b_334_ = v___y_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object* v___x_344_, lean_object* v_linter_345_, lean_object* v_as_346_, lean_object* v_i_347_, lean_object* v_stop_348_, lean_object* v_b_349_){
_start:
{
size_t v_i_boxed_350_; size_t v_stop_boxed_351_; lean_object* v_res_352_; 
v_i_boxed_350_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_348_);
lean_dec(v_stop_348_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_344_, v_linter_345_, v_as_346_, v_i_boxed_350_, v_stop_boxed_351_, v_b_349_);
lean_dec_ref(v_as_346_);
lean_dec_ref(v_linter_345_);
return v_res_352_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_353_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_357_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_ctor_set(v___x_357_, 4, v___x_356_);
lean_ctor_set(v___x_357_, 5, v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_unsigned_to_nat(32u);
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
lean_ctor_set(v___x_362_, 3, v___x_361_);
lean_ctor_set(v___x_362_, 4, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v_test_365_, lean_object* v_v_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; size_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_371_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
lean_inc_n(v___x_363_, 5);
v___x_372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_372_, 0, v___x_363_);
lean_ctor_set(v___x_372_, 1, v___x_363_);
lean_ctor_set(v___x_372_, 2, v___x_363_);
lean_ctor_set(v___x_372_, 3, v___x_363_);
lean_ctor_set(v___x_372_, 4, v___x_371_);
lean_ctor_set(v___x_372_, 5, v___x_371_);
lean_ctor_set(v___x_372_, 6, v___x_371_);
lean_ctor_set(v___x_372_, 7, v___x_371_);
lean_ctor_set(v___x_372_, 8, v___x_371_);
lean_ctor_set(v___x_372_, 9, v___x_371_);
v___x_373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2);
v___x_374_ = lean_unsigned_to_nat(32u);
v___x_375_ = lean_mk_empty_array_with_capacity(v___x_374_);
v___x_376_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3);
v___x_377_ = ((size_t)5ULL);
v___x_378_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_375_);
lean_ctor_set(v___x_378_, 2, v___x_363_);
lean_ctor_set(v___x_378_, 3, v___x_363_);
lean_ctor_set_usize(v___x_378_, 4, v___x_377_);
v___x_379_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4);
v___x_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_380_, 0, v___x_372_);
lean_ctor_set(v___x_380_, 1, v___x_373_);
lean_ctor_set(v___x_380_, 2, v___x_364_);
lean_ctor_set(v___x_380_, 3, v___x_378_);
lean_ctor_set(v___x_380_, 4, v___x_379_);
v___x_381_ = lean_st_mk_ref(v___x_380_);
v___x_382_ = l_Lean_Elab_Command_mkMetaContext;
lean_inc(v___y_369_);
lean_inc_ref(v___y_368_);
lean_inc(v___x_381_);
v___x_383_ = lean_apply_6(v_test_365_, v_v_366_, v___x_382_, v___x_381_, v___y_368_, v___y_369_, lean_box(0));
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_st_ref_get(v___x_381_);
lean_dec(v___x_381_);
lean_dec(v___x_388_);
if (v_isShared_387_ == 0)
{
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_384_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_dec(v___x_381_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v_test_395_, lean_object* v_v_396_, lean_object* v_x_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(v___x_393_, v___x_394_, v_test_395_, v_v_396_, v_x_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object* v_a_402_, lean_object* v___x_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_apply_2(v_a_402_, v___x_403_, lean_box(0));
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_414_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_405_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_405_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object* v_a_422_, lean_object* v___x_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(v_a_422_, v___x_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object* v_linter_426_, size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec_ref(v_linter_426_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_bs_429_);
return v___x_434_;
}
else
{
lean_object* v_toEnvLinter_435_; lean_object* v_test_436_; lean_object* v_v_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_toEnvLinter_435_ = lean_ctor_get(v_linter_426_, 0);
v_test_436_ = lean_ctor_get(v_toEnvLinter_435_, 0);
v_v_437_ = lean_array_uget(v_bs_429_, v_i_428_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_box(1);
lean_inc(v_v_437_);
lean_inc_ref(v_test_436_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed), 8, 4);
lean_closure_set(v___f_440_, 0, v___x_438_);
lean_closure_set(v___f_440_, 1, v___x_439_);
lean_closure_set(v___f_440_, 2, v_test_436_);
lean_closure_set(v___f_440_, 3, v_v_437_);
v___x_441_ = lean_box(0);
v___x_442_ = l_Lean_Core_wrapAsync___redArg(v___f_440_, v___x_441_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v_bs_x27_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = lean_box(0);
v___f_445_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_445_, 0, v_a_443_);
lean_closure_set(v___f_445_, 1, v___x_444_);
v___x_446_ = lean_io_as_task(v___f_445_, v___x_438_);
v_bs_x27_447_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_438_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_v_437_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_428_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_447_, v_i_428_, v___x_448_);
v_i_428_ = v___x_450_;
v_bs_429_ = v___x_451_;
goto _start;
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_v_437_);
lean_dec_ref(v_bs_429_);
lean_dec_ref(v_linter_426_);
v_a_453_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_442_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_442_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object* v_linter_461_, lean_object* v_sz_462_, lean_object* v_i_463_, lean_object* v_bs_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
size_t v_sz_boxed_468_; size_t v_i_boxed_469_; lean_object* v_res_470_; 
v_sz_boxed_468_ = lean_unbox_usize(v_sz_462_);
lean_dec(v_sz_462_);
v_i_boxed_469_ = lean_unbox_usize(v_i_463_);
lean_dec(v_i_463_);
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_linter_461_, v_sz_boxed_468_, v_i_boxed_469_, v_bs_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(lean_object* v_decls_473_, lean_object* v___x_474_, size_t v_sz_475_, size_t v_i_476_, lean_object* v_bs_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_lt(v_i_476_, v_sz_475_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v___x_474_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_bs_477_);
return v___x_482_;
}
else
{
lean_object* v_v_483_; lean_object* v___x_484_; lean_object* v_bs_x27_485_; lean_object* v___y_487_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_v_483_ = lean_array_uget(v_bs_477_, v_i_476_);
v___x_484_ = lean_unsigned_to_nat(0u);
v_bs_x27_485_ = lean_array_uset(v_bs_477_, v_i_476_, v___x_484_);
v___x_497_ = lean_array_get_size(v_decls_473_);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_499_ = lean_nat_dec_lt(v___x_484_, v___x_497_);
if (v___x_499_ == 0)
{
v___y_487_ = v___x_498_;
goto v___jp_486_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = lean_nat_dec_le(v___x_497_, v___x_497_);
if (v___x_500_ == 0)
{
if (v___x_499_ == 0)
{
v___y_487_ = v___x_498_;
goto v___jp_486_;
}
else
{
size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((size_t)0ULL);
v___x_502_ = lean_usize_of_nat(v___x_497_);
lean_inc_ref(v___x_474_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_474_, v_v_483_, v_decls_473_, v___x_501_, v___x_502_, v___x_498_);
v___y_487_ = v___x_503_;
goto v___jp_486_;
}
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((size_t)0ULL);
v___x_505_ = lean_usize_of_nat(v___x_497_);
lean_inc_ref(v___x_474_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_474_, v_v_483_, v_decls_473_, v___x_504_, v___x_505_, v___x_498_);
v___y_487_ = v___x_506_;
goto v___jp_486_;
}
}
v___jp_486_:
{
size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; 
v_sz_488_ = lean_array_size(v___y_487_);
v___x_489_ = ((size_t)0ULL);
lean_inc(v_v_483_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_483_, v_sz_488_, v___x_489_, v___y_487_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_v_483_);
lean_ctor_set(v___x_492_, 1, v_a_491_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_476_, v___x_493_);
v___x_495_ = lean_array_uset(v_bs_x27_485_, v_i_476_, v___x_492_);
v_i_476_ = v___x_494_;
v_bs_477_ = v___x_495_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_485_);
lean_dec(v_v_483_);
lean_dec_ref(v___x_474_);
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___boxed(lean_object* v_decls_507_, lean_object* v___x_508_, lean_object* v_sz_509_, lean_object* v_i_510_, lean_object* v_bs_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v_sz_boxed_515_ = lean_unbox_usize(v_sz_509_);
lean_dec(v_sz_509_);
v_i_boxed_516_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(v_decls_507_, v___x_508_, v_sz_boxed_515_, v_i_boxed_516_, v_bs_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_decls_507_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object* v___x_518_, lean_object* v_decls_519_, size_t v_sz_520_, size_t v_i_521_, lean_object* v_bs_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = lean_usize_dec_lt(v_i_521_, v_sz_520_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec_ref(v___x_518_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v_bs_522_);
return v___x_527_;
}
else
{
lean_object* v_v_528_; lean_object* v___x_529_; lean_object* v_bs_x27_530_; lean_object* v___y_532_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_v_528_ = lean_array_uget(v_bs_522_, v_i_521_);
v___x_529_ = lean_unsigned_to_nat(0u);
v_bs_x27_530_ = lean_array_uset(v_bs_522_, v_i_521_, v___x_529_);
v___x_542_ = lean_array_get_size(v_decls_519_);
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_544_ = lean_nat_dec_lt(v___x_529_, v___x_542_);
if (v___x_544_ == 0)
{
v___y_532_ = v___x_543_;
goto v___jp_531_;
}
else
{
uint8_t v___x_545_; 
v___x_545_ = lean_nat_dec_le(v___x_542_, v___x_542_);
if (v___x_545_ == 0)
{
if (v___x_544_ == 0)
{
v___y_532_ = v___x_543_;
goto v___jp_531_;
}
else
{
size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v___x_546_ = ((size_t)0ULL);
v___x_547_ = lean_usize_of_nat(v___x_542_);
lean_inc_ref(v___x_518_);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_518_, v_v_528_, v_decls_519_, v___x_546_, v___x_547_, v___x_543_);
v___y_532_ = v___x_548_;
goto v___jp_531_;
}
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_542_);
lean_inc_ref(v___x_518_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v___x_518_, v_v_528_, v_decls_519_, v___x_549_, v___x_550_, v___x_543_);
v___y_532_ = v___x_551_;
goto v___jp_531_;
}
}
v___jp_531_:
{
size_t v_sz_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_sz_533_ = lean_array_size(v___y_532_);
v___x_534_ = ((size_t)0ULL);
lean_inc(v_v_528_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_528_, v_sz_533_, v___x_534_, v___y_532_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_v_528_);
lean_ctor_set(v___x_537_, 1, v_a_536_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_521_, v___x_538_);
v___x_540_ = lean_array_uset(v_bs_x27_530_, v_i_521_, v___x_537_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7(v_decls_519_, v___x_518_, v_sz_520_, v___x_539_, v___x_540_, v___y_523_, v___y_524_);
return v___x_541_;
}
else
{
lean_dec_ref(v_bs_x27_530_);
lean_dec(v_v_528_);
lean_dec_ref(v___x_518_);
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object* v___x_552_, lean_object* v_decls_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_bs_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v_sz_boxed_560_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_561_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v___x_552_, v_decls_553_, v_sz_boxed_560_, v_i_boxed_561_, v_bs_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v_decls_553_);
return v_res_562_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_563_; uint64_t v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1723u);
v___x_564_ = lean_uint64_of_nat(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
return v_x_565_;
}
else
{
lean_object* v_key_567_; lean_object* v_value_568_; lean_object* v_tail_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_595_; 
v_key_567_ = lean_ctor_get(v_x_566_, 0);
v_value_568_ = lean_ctor_get(v_x_566_, 1);
v_tail_569_ = lean_ctor_get(v_x_566_, 2);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_595_ == 0)
{
v___x_571_ = v_x_566_;
v_isShared_572_ = v_isSharedCheck_595_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_tail_569_);
lean_inc(v_value_568_);
lean_inc(v_key_567_);
lean_dec(v_x_566_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_595_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; uint64_t v___y_575_; 
v___x_573_ = lean_array_get_size(v_x_565_);
if (lean_obj_tag(v_key_567_) == 0)
{
uint64_t v___x_593_; 
v___x_593_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_575_ = v___x_593_;
goto v___jp_574_;
}
else
{
uint64_t v_hash_594_; 
v_hash_594_ = lean_ctor_get_uint64(v_key_567_, sizeof(void*)*2);
v___y_575_ = v_hash_594_;
goto v___jp_574_;
}
v___jp_574_:
{
uint64_t v___x_576_; uint64_t v___x_577_; uint64_t v_fold_578_; uint64_t v___x_579_; uint64_t v___x_580_; uint64_t v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_576_ = 32ULL;
v___x_577_ = lean_uint64_shift_right(v___y_575_, v___x_576_);
v_fold_578_ = lean_uint64_xor(v___y_575_, v___x_577_);
v___x_579_ = 16ULL;
v___x_580_ = lean_uint64_shift_right(v_fold_578_, v___x_579_);
v___x_581_ = lean_uint64_xor(v_fold_578_, v___x_580_);
v___x_582_ = lean_uint64_to_usize(v___x_581_);
v___x_583_ = lean_usize_of_nat(v___x_573_);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_sub(v___x_583_, v___x_584_);
v___x_586_ = lean_usize_land(v___x_582_, v___x_585_);
v___x_587_ = lean_array_uget_borrowed(v_x_565_, v___x_586_);
lean_inc(v___x_587_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 2, v___x_587_);
v___x_589_ = v___x_571_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_key_567_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_value_568_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v___x_587_);
v___x_589_ = v_reuseFailAlloc_592_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = lean_array_uset(v_x_565_, v___x_586_, v___x_589_);
v_x_565_ = v___x_590_;
v_x_566_ = v_tail_569_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_596_, lean_object* v_source_597_, lean_object* v_target_598_){
_start:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_array_get_size(v_source_597_);
v___x_600_ = lean_nat_dec_lt(v_i_596_, v___x_599_);
if (v___x_600_ == 0)
{
lean_dec_ref(v_source_597_);
lean_dec(v_i_596_);
return v_target_598_;
}
else
{
lean_object* v_es_601_; lean_object* v___x_602_; lean_object* v_source_603_; lean_object* v_target_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_es_601_ = lean_array_fget(v_source_597_, v_i_596_);
v___x_602_ = lean_box(0);
v_source_603_ = lean_array_fset(v_source_597_, v_i_596_, v___x_602_);
v_target_604_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(v_target_598_, v_es_601_);
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_add(v_i_596_, v___x_605_);
lean_dec(v_i_596_);
v_i_596_ = v___x_606_;
v_source_597_ = v_source_603_;
v_target_598_ = v_target_604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object* v_data_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_nbuckets_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_609_ = lean_array_get_size(v_data_608_);
v___x_610_ = lean_unsigned_to_nat(2u);
v_nbuckets_611_ = lean_nat_mul(v___x_609_, v___x_610_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_box(0);
v___x_614_ = lean_mk_array(v_nbuckets_611_, v___x_613_);
v___x_615_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v___x_612_, v_data_608_, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object* v_a_616_, lean_object* v_b_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_dec(v_b_617_);
lean_dec(v_a_616_);
return v_x_618_;
}
else
{
lean_object* v_key_619_; lean_object* v_value_620_; lean_object* v_tail_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
v_key_619_ = lean_ctor_get(v_x_618_, 0);
v_value_620_ = lean_ctor_get(v_x_618_, 1);
v_tail_621_ = lean_ctor_get(v_x_618_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_633_ == 0)
{
v___x_623_ = v_x_618_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tail_621_);
lean_inc(v_value_620_);
lean_inc(v_key_619_);
lean_dec(v_x_618_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___x_625_; 
v___x_625_ = lean_name_eq(v_key_619_, v_a_616_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_616_, v_b_617_, v_tail_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 2, v___x_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_key_619_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_value_620_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_value_620_);
lean_dec(v_key_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_b_617_);
lean_ctor_set(v___x_623_, 0, v_a_616_);
v___x_631_ = v___x_623_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_b_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_tail_621_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
else
{
lean_object* v_key_637_; lean_object* v_tail_638_; uint8_t v___x_639_; 
v_key_637_ = lean_ctor_get(v_x_635_, 0);
v_tail_638_ = lean_ctor_get(v_x_635_, 2);
v___x_639_ = lean_name_eq(v_key_637_, v_a_634_);
if (v___x_639_ == 0)
{
v_x_635_ = v_tail_638_;
goto _start;
}
else
{
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_641_, lean_object* v_x_642_){
_start:
{
uint8_t v_res_643_; lean_object* v_r_644_; 
v_res_643_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_641_, v_x_642_);
lean_dec(v_x_642_);
lean_dec(v_a_641_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object* v_m_645_, lean_object* v_a_646_, lean_object* v_b_647_){
_start:
{
lean_object* v_size_648_; lean_object* v_buckets_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_695_; 
v_size_648_ = lean_ctor_get(v_m_645_, 0);
v_buckets_649_ = lean_ctor_get(v_m_645_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_m_645_);
if (v_isSharedCheck_695_ == 0)
{
v___x_651_ = v_m_645_;
v_isShared_652_ = v_isSharedCheck_695_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_buckets_649_);
lean_inc(v_size_648_);
lean_dec(v_m_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_695_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint64_t v___y_655_; 
v___x_653_ = lean_array_get_size(v_buckets_649_);
if (lean_obj_tag(v_a_646_) == 0)
{
uint64_t v___x_693_; 
v___x_693_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_655_ = v___x_693_;
goto v___jp_654_;
}
else
{
uint64_t v_hash_694_; 
v_hash_694_ = lean_ctor_get_uint64(v_a_646_, sizeof(void*)*2);
v___y_655_ = v_hash_694_;
goto v___jp_654_;
}
v___jp_654_:
{
uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v_fold_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v_bkt_667_; uint8_t v___x_668_; 
v___x_656_ = 32ULL;
v___x_657_ = lean_uint64_shift_right(v___y_655_, v___x_656_);
v_fold_658_ = lean_uint64_xor(v___y_655_, v___x_657_);
v___x_659_ = 16ULL;
v___x_660_ = lean_uint64_shift_right(v_fold_658_, v___x_659_);
v___x_661_ = lean_uint64_xor(v_fold_658_, v___x_660_);
v___x_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = lean_usize_of_nat(v___x_653_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_sub(v___x_663_, v___x_664_);
v___x_666_ = lean_usize_land(v___x_662_, v___x_665_);
v_bkt_667_ = lean_array_uget_borrowed(v_buckets_649_, v___x_666_);
v___x_668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_646_, v_bkt_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v_size_x27_670_; lean_object* v___x_671_; lean_object* v_buckets_x27_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v_size_x27_670_ = lean_nat_add(v_size_648_, v___x_669_);
lean_dec(v_size_648_);
lean_inc(v_bkt_667_);
v___x_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_671_, 0, v_a_646_);
lean_ctor_set(v___x_671_, 1, v_b_647_);
lean_ctor_set(v___x_671_, 2, v_bkt_667_);
v_buckets_x27_672_ = lean_array_uset(v_buckets_649_, v___x_666_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(4u);
v___x_674_ = lean_nat_mul(v_size_x27_670_, v___x_673_);
v___x_675_ = lean_unsigned_to_nat(3u);
v___x_676_ = lean_nat_div(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_array_get_size(v_buckets_x27_672_);
v___x_678_ = lean_nat_dec_le(v___x_676_, v___x_677_);
lean_dec(v___x_676_);
if (v___x_678_ == 0)
{
lean_object* v_val_679_; lean_object* v___x_681_; 
v_val_679_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_buckets_x27_672_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_val_679_);
lean_ctor_set(v___x_651_, 0, v_size_x27_670_);
v___x_681_ = v___x_651_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_x27_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_val_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v___x_684_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_buckets_x27_672_);
lean_ctor_set(v___x_651_, 0, v_size_x27_670_);
v___x_684_ = v___x_651_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_size_x27_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_buckets_x27_672_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
lean_object* v___x_686_; lean_object* v_buckets_x27_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_inc(v_bkt_667_);
v___x_686_ = lean_box(0);
v_buckets_x27_687_ = lean_array_uset(v_buckets_649_, v___x_666_, v___x_686_);
v___x_688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_646_, v_b_647_, v_bkt_667_);
v___x_689_ = lean_array_uset(v_buckets_x27_687_, v___x_666_, v___x_688_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_689_);
v___x_691_ = v___x_651_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_size_648_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object* v_as_699_, size_t v_sz_700_, size_t v_i_701_, lean_object* v_b_702_){
_start:
{
lean_object* v_a_705_; uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_lt(v_i_701_, v_sz_700_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_b_702_);
return v___x_710_;
}
else
{
lean_object* v_a_711_; lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_729_; 
v_a_711_ = lean_array_uget(v_as_699_, v_i_701_);
v_fst_712_ = lean_ctor_get(v_a_711_, 0);
v_snd_713_ = lean_ctor_get(v_a_711_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_729_ == 0)
{
v___x_715_ = v_a_711_;
v_isShared_716_ = v_isSharedCheck_729_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_snd_713_);
lean_inc(v_fst_712_);
lean_dec(v_a_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_729_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_val_718_; lean_object* v___x_720_; 
v___x_720_ = lean_task_get_own(v_snd_713_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1);
v___x_723_ = l_Lean_Exception_toMessageData(v_a_721_);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 7);
lean_ctor_set(v___x_715_, 1, v___x_723_);
lean_ctor_set(v___x_715_, 0, v___x_722_);
v___x_725_ = v___x_715_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v_val_718_ = v___x_725_;
goto v___jp_717_;
}
}
else
{
lean_object* v_a_727_; 
lean_del_object(v___x_715_);
v_a_727_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_720_, 1);
if (lean_obj_tag(v_a_727_) == 1)
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_a_727_, 1);
v_val_718_ = v_val_728_;
goto v___jp_717_;
}
else
{
lean_dec(v_a_727_);
lean_dec(v_fst_712_);
v_a_705_ = v_b_702_;
goto v___jp_704_;
}
}
v___jp_717_:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_702_, v_fst_712_, v_val_718_);
v_a_705_ = v___x_719_;
goto v___jp_704_;
}
}
}
v___jp_704_:
{
size_t v___x_706_; size_t v___x_707_; 
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_701_, v___x_706_);
v_i_701_ = v___x_707_;
v_b_702_ = v_a_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object* v_as_730_, lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_b_733_, lean_object* v___y_734_){
_start:
{
size_t v_sz_boxed_735_; size_t v_i_boxed_736_; lean_object* v_res_737_; 
v_sz_boxed_735_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_736_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_730_, v_sz_boxed_735_, v_i_boxed_736_, v_b_733_);
lean_dec_ref(v_as_730_);
return v_res_737_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = lean_unsigned_to_nat(16u);
v___x_740_ = lean_mk_array(v___x_739_, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(size_t v_sz_744_, size_t v_i_745_, lean_object* v_bs_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_bs_746_);
return v___x_751_;
}
else
{
lean_object* v_v_752_; lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_780_; 
v_v_752_ = lean_array_uget(v_bs_746_, v_i_745_);
v_fst_753_ = lean_ctor_get(v_v_752_, 0);
v_snd_754_ = lean_ctor_get(v_v_752_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_v_752_);
if (v_isSharedCheck_780_ == 0)
{
v___x_756_ = v_v_752_;
v_isShared_757_ = v_isSharedCheck_780_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_snd_754_);
lean_inc(v_fst_753_);
lean_dec(v_v_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_780_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; size_t v_sz_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v_sz_760_ = lean_array_size(v_snd_754_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_snd_754_, v_sz_760_, v___x_761_, v___x_759_);
lean_dec(v_snd_754_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_bs_x27_764_; lean_object* v___x_766_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_bs_x27_764_ = lean_array_uset(v_bs_746_, v_i_745_, v___x_758_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_a_763_);
v___x_766_ = v___x_756_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_753_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_a_763_);
v___x_766_ = v_reuseFailAlloc_771_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_745_, v___x_767_);
v___x_769_ = lean_array_uset(v_bs_x27_764_, v_i_745_, v___x_766_);
v_i_745_ = v___x_768_;
v_bs_746_ = v___x_769_;
goto _start;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_del_object(v___x_756_);
lean_dec(v_fst_753_);
lean_dec_ref(v_bs_746_);
v_a_772_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_762_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object* v_sz_781_, lean_object* v_i_782_, lean_object* v_bs_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
size_t v_sz_boxed_787_; size_t v_i_boxed_788_; lean_object* v_res_789_; 
v_sz_boxed_787_ = lean_unbox_usize(v_sz_781_);
lean_dec(v_sz_781_);
v_i_boxed_788_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_sz_boxed_787_, v_i_boxed_788_, v_bs_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object* v_decls_790_, lean_object* v_linters_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_env_796_; size_t v_sz_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___x_795_ = lean_st_ref_get(v_a_793_);
v_env_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref(v_env_796_);
lean_dec(v___x_795_);
v_sz_797_ = lean_array_size(v_linters_791_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_env_796_, v_decls_790_, v_sz_797_, v___x_798_, v_linters_791_, v_a_792_, v_a_793_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; size_t v_sz_801_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v_sz_801_ = lean_array_size(v_a_800_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_sz_801_, v___x_798_, v_a_800_, v_a_792_, v_a_793_);
return v___x_802_;
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_a_803_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_799_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_799_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object* v_decls_811_, lean_object* v_linters_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Linter_EnvLinter_lintCore(v_decls_811_, v_linters_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec_ref(v_decls_811_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object* v_00_u03b2_817_, lean_object* v_m_818_, lean_object* v_a_819_, lean_object* v_b_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_m_818_, v_a_819_, v_b_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object* v_as_822_, size_t v_sz_823_, size_t v_i_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_822_, v_sz_823_, v_i_824_, v_b_825_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object* v_as_830_, lean_object* v_sz_831_, lean_object* v_i_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_831_);
lean_dec(v_sz_831_);
v_i_boxed_838_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(v_as_830_, v_sz_boxed_837_, v_i_boxed_838_, v_b_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_as_830_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(v_00_u03b2_844_, v_a_845_, v_x_846_);
lean_dec(v_x_846_);
lean_dec(v_a_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object* v_00_u03b2_849_, lean_object* v_data_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_data_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_b_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_853_, v_b_854_, v_x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_857_, lean_object* v_i_858_, lean_object* v_source_859_, lean_object* v_target_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v_i_858_, v_source_859_, v_target_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object* v_a_866_, lean_object* v_fallback_867_, lean_object* v_x_868_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_inc(v_fallback_867_);
return v_fallback_867_;
}
else
{
lean_object* v_key_869_; lean_object* v_value_870_; lean_object* v_tail_871_; uint8_t v___x_872_; 
v_key_869_ = lean_ctor_get(v_x_868_, 0);
v_value_870_ = lean_ctor_get(v_x_868_, 1);
v_tail_871_ = lean_ctor_get(v_x_868_, 2);
v___x_872_ = lean_name_eq(v_key_869_, v_a_866_);
if (v___x_872_ == 0)
{
v_x_868_ = v_tail_871_;
goto _start;
}
else
{
lean_inc(v_value_870_);
return v_value_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object* v_a_874_, lean_object* v_fallback_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_874_, v_fallback_875_, v_x_876_);
lean_dec(v_x_876_);
lean_dec(v_fallback_875_);
lean_dec(v_a_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object* v_m_878_, lean_object* v_a_879_, lean_object* v_fallback_880_){
_start:
{
lean_object* v_buckets_881_; lean_object* v___x_882_; uint64_t v___y_884_; 
v_buckets_881_ = lean_ctor_get(v_m_878_, 1);
v___x_882_ = lean_array_get_size(v_buckets_881_);
if (lean_obj_tag(v_a_879_) == 0)
{
uint64_t v___x_898_; 
v___x_898_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_884_ = v___x_898_;
goto v___jp_883_;
}
else
{
uint64_t v_hash_899_; 
v_hash_899_ = lean_ctor_get_uint64(v_a_879_, sizeof(void*)*2);
v___y_884_ = v_hash_899_;
goto v___jp_883_;
}
v___jp_883_:
{
uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v_fold_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_885_ = 32ULL;
v___x_886_ = lean_uint64_shift_right(v___y_884_, v___x_885_);
v_fold_887_ = lean_uint64_xor(v___y_884_, v___x_886_);
v___x_888_ = 16ULL;
v___x_889_ = lean_uint64_shift_right(v_fold_887_, v___x_888_);
v___x_890_ = lean_uint64_xor(v_fold_887_, v___x_889_);
v___x_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = lean_usize_of_nat(v___x_882_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_sub(v___x_892_, v___x_893_);
v___x_895_ = lean_usize_land(v___x_891_, v___x_894_);
v___x_896_ = lean_array_uget_borrowed(v_buckets_881_, v___x_895_);
v___x_897_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_879_, v_fallback_880_, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object* v_m_900_, lean_object* v_a_901_, lean_object* v_fallback_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_900_, v_a_901_, v_fallback_902_);
lean_dec(v_fallback_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_m_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object* v_a_904_, lean_object* v_hi_905_, lean_object* v_pivot_906_, lean_object* v_as_907_, lean_object* v_i_908_, lean_object* v_k_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_nat_dec_lt(v_k_909_, v_hi_905_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v_k_909_);
v___x_911_ = lean_array_fswap(v_as_907_, v_i_908_, v_hi_905_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_i_908_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v_fst_914_; lean_object* v_fst_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_913_ = lean_array_fget_borrowed(v_as_907_, v_k_909_);
v_fst_914_ = lean_ctor_get(v___x_913_, 0);
v_fst_915_ = lean_ctor_get(v_pivot_906_, 0);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_904_, v_fst_914_, v___x_916_);
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_904_, v_fst_915_, v___x_916_);
v___x_919_ = lean_nat_dec_lt(v___x_917_, v___x_918_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_k_909_, v___x_920_);
lean_dec(v_k_909_);
v_k_909_ = v___x_921_;
goto _start;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = lean_array_fswap(v_as_907_, v_i_908_, v_k_909_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_add(v_i_908_, v___x_924_);
lean_dec(v_i_908_);
v___x_926_ = lean_nat_add(v_k_909_, v___x_924_);
lean_dec(v_k_909_);
v_as_907_ = v___x_923_;
v_i_908_ = v___x_925_;
v_k_909_ = v___x_926_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object* v_a_928_, lean_object* v_hi_929_, lean_object* v_pivot_930_, lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_k_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_928_, v_hi_929_, v_pivot_930_, v_as_931_, v_i_932_, v_k_933_);
lean_dec_ref(v_pivot_930_);
lean_dec(v_hi_929_);
lean_dec_ref(v_a_928_);
return v_res_934_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object* v_a_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_fst_938_; lean_object* v_fst_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_fst_938_ = lean_ctor_get(v_x_936_, 0);
v_fst_939_ = lean_ctor_get(v_x_937_, 0);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_935_, v_fst_938_, v___x_940_);
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_935_, v_fst_939_, v___x_940_);
v___x_943_ = lean_nat_dec_lt(v___x_941_, v___x_942_);
lean_dec(v___x_942_);
lean_dec(v___x_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object* v_a_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_944_, v_x_945_, v_x_946_);
lean_dec_ref(v_x_946_);
lean_dec_ref(v_x_945_);
lean_dec_ref(v_a_944_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object* v_a_949_, lean_object* v_n_950_, lean_object* v_as_951_, lean_object* v_lo_952_, lean_object* v_hi_953_){
_start:
{
lean_object* v___y_955_; uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_lt(v_lo_952_, v_hi_953_);
if (v___x_965_ == 0)
{
lean_dec(v_lo_952_);
return v_as_951_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_mid_968_; lean_object* v___y_970_; lean_object* v___y_976_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_966_ = lean_nat_add(v_lo_952_, v_hi_953_);
v___x_967_ = lean_unsigned_to_nat(1u);
v_mid_968_ = lean_nat_shiftr(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
v___x_981_ = lean_array_fget_borrowed(v_as_951_, v_mid_968_);
v___x_982_ = lean_array_fget_borrowed(v_as_951_, v_lo_952_);
v___x_983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_949_, v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
v___y_976_ = v_as_951_;
goto v___jp_975_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = lean_array_fswap(v_as_951_, v_lo_952_, v_mid_968_);
v___y_976_ = v___x_984_;
goto v___jp_975_;
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_fget_borrowed(v___y_970_, v_mid_968_);
v___x_972_ = lean_array_fget_borrowed(v___y_970_, v_hi_953_);
v___x_973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_949_, v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec(v_mid_968_);
v___y_955_ = v___y_970_;
goto v___jp_954_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_fswap(v___y_970_, v_mid_968_, v_hi_953_);
lean_dec(v_mid_968_);
v___y_955_ = v___x_974_;
goto v___jp_954_;
}
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_array_fget_borrowed(v___y_976_, v_hi_953_);
v___x_978_ = lean_array_fget_borrowed(v___y_976_, v_lo_952_);
v___x_979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_949_, v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
v___y_970_ = v___y_976_;
goto v___jp_969_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = lean_array_fswap(v___y_976_, v_lo_952_, v_hi_953_);
v___y_970_ = v___x_980_;
goto v___jp_969_;
}
}
}
v___jp_954_:
{
lean_object* v_pivot_956_; lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; uint8_t v___x_960_; 
v_pivot_956_ = lean_array_fget(v___y_955_, v_hi_953_);
lean_inc_n(v_lo_952_, 2);
v___x_957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_949_, v_hi_953_, v_pivot_956_, v___y_955_, v_lo_952_, v_lo_952_);
lean_dec(v_pivot_956_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_fst_958_);
v_snd_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_957_);
v___x_960_ = lean_nat_dec_le(v_hi_953_, v_fst_958_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_949_, v_n_950_, v_snd_959_, v_lo_952_, v_fst_958_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_fst_958_, v___x_962_);
lean_dec(v_fst_958_);
v_as_951_ = v___x_961_;
v_lo_952_ = v___x_963_;
goto _start;
}
else
{
lean_dec(v_fst_958_);
lean_dec(v_lo_952_);
return v_snd_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object* v_a_985_, lean_object* v_n_986_, lean_object* v_as_987_, lean_object* v_lo_988_, lean_object* v_hi_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_985_, v_n_986_, v_as_987_, v_lo_988_, v_hi_989_);
lean_dec(v_hi_989_);
lean_dec(v_n_986_);
lean_dec_ref(v_a_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object* v_declName_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; lean_object* v_env_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_994_ = lean_st_ref_get(v___y_992_);
v_env_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc_ref(v_env_995_);
lean_dec(v___x_994_);
v___x_996_ = l_Lean_isRecCore(v_env_995_, v_declName_991_);
v___x_997_ = lean_box(v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object* v_declName_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_999_, v___y_1000_);
lean_dec(v___y_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object* v_declName_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v_env_1007_; lean_object* v___x_1008_; lean_object* v_env_1009_; lean_object* v___x_1010_; lean_object* v_toEnvExtension_1011_; lean_object* v_asyncMode_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1006_ = lean_st_ref_get(v___y_1004_);
v_env_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc_ref(v_env_1007_);
lean_dec(v___x_1006_);
v___x_1008_ = lean_st_ref_get(v___y_1004_);
v_env_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1009_);
lean_dec(v___x_1008_);
v___x_1010_ = l_Lean_declRangeExt;
v_toEnvExtension_1011_ = lean_ctor_get(v___x_1010_, 0);
v_asyncMode_1012_ = lean_ctor_get(v_toEnvExtension_1011_, 2);
v___x_1013_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1014_ = 0;
lean_inc(v_declName_1003_);
v___x_1015_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1013_, v___x_1010_, v_env_1007_, v_declName_1003_, v_asyncMode_1012_, v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = 1;
v___x_1017_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1013_, v___x_1010_, v_env_1009_, v_declName_1003_, v_asyncMode_1012_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declName_1003_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1015_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1020_, v___y_1021_);
lean_dec(v___y_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object* v_declName_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_ranges_1029_; lean_object* v___x_1035_; lean_object* v_env_1036_; lean_object* v___x_1037_; lean_object* v_a_1038_; uint8_t v___y_1044_; uint8_t v___x_1048_; 
v___x_1035_ = lean_st_ref_get(v___y_1026_);
v_env_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref_n(v_env_1036_, 2);
lean_dec(v___x_1035_);
lean_inc_n(v_declName_1024_, 2);
v___x_1037_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1024_, v___y_1026_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v___x_1037_);
v___x_1048_ = l_Lean_isAuxRecursor(v_env_1036_, v_declName_1024_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; 
lean_inc(v_declName_1024_);
v___x_1049_ = l_Lean_isNoConfusion(v_env_1036_, v_declName_1024_);
v___y_1044_ = v___x_1049_;
goto v___jp_1043_;
}
else
{
lean_dec_ref(v_env_1036_);
v___y_1044_ = v___x_1048_;
goto v___jp_1043_;
}
v___jp_1028_:
{
if (lean_obj_tag(v_ranges_1029_) == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = l_Lean_builtinDeclRanges;
v___x_1031_ = lean_st_ref_get(v___x_1030_);
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1031_, v_declName_1024_);
lean_dec(v_declName_1024_);
lean_dec(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_declName_1024_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_ranges_1029_);
return v___x_1034_;
}
}
v___jp_1039_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_a_1042_; 
v___x_1040_ = l_Lean_Name_getPrefix(v_declName_1024_);
v___x_1041_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v___x_1040_, v___y_1026_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v_ranges_1029_ = v_a_1042_;
goto v___jp_1028_;
}
v___jp_1043_:
{
if (v___y_1044_ == 0)
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_unbox(v_a_1038_);
lean_dec(v_a_1038_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v_a_1047_; 
lean_inc(v_declName_1024_);
v___x_1046_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1024_, v___y_1026_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1046_);
v_ranges_1029_ = v_a_1047_;
goto v___jp_1028_;
}
else
{
goto v___jp_1039_;
}
}
else
{
lean_dec(v_a_1038_);
goto v___jp_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object* v_declName_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object* v_as_1055_, size_t v_sz_1056_, size_t v_i_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1057_, v_sz_1056_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1058_);
return v___x_1063_;
}
else
{
lean_object* v_a_1064_; lean_object* v_fst_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_array_uget_borrowed(v_as_1055_, v_i_1057_);
v_fst_1065_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fst_1065_);
v___x_1066_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_fst_1065_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v_a_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
if (lean_obj_tag(v_a_1067_) == 1)
{
lean_object* v_val_1073_; lean_object* v_range_1074_; lean_object* v_pos_1075_; lean_object* v_line_1076_; lean_object* v___x_1077_; 
v_val_1073_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v_a_1067_, 1);
v_range_1074_ = lean_ctor_get(v_val_1073_, 0);
lean_inc_ref(v_range_1074_);
lean_dec(v_val_1073_);
v_pos_1075_ = lean_ctor_get(v_range_1074_, 0);
lean_inc_ref(v_pos_1075_);
lean_dec_ref(v_range_1074_);
v_line_1076_ = lean_ctor_get(v_pos_1075_, 0);
lean_inc(v_line_1076_);
lean_dec_ref(v_pos_1075_);
lean_inc(v_fst_1065_);
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_1058_, v_fst_1065_, v_line_1076_);
v_a_1069_ = v___x_1077_;
goto v___jp_1068_;
}
else
{
lean_dec(v_a_1067_);
v_a_1069_ = v_b_1058_;
goto v___jp_1068_;
}
v___jp_1068_:
{
size_t v___x_1070_; size_t v___x_1071_; 
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1057_, v___x_1070_);
v_i_1057_ = v___x_1071_;
v_b_1058_ = v_a_1069_;
goto _start;
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_b_1058_);
v_a_1078_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1066_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1066_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object* v_as_1086_, lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
size_t v_sz_boxed_1093_; size_t v_i_boxed_1094_; lean_object* v_res_1095_; 
v_sz_boxed_1093_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1094_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1086_, v_sz_boxed_1093_, v_i_boxed_1094_, v_b_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_as_1086_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
return v_x_1096_;
}
else
{
lean_object* v_key_1098_; lean_object* v_value_1099_; lean_object* v_tail_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_key_1098_ = lean_ctor_get(v_x_1097_, 0);
v_value_1099_ = lean_ctor_get(v_x_1097_, 1);
v_tail_1100_ = lean_ctor_get(v_x_1097_, 2);
lean_inc(v_value_1099_);
lean_inc(v_key_1098_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_key_1098_);
lean_ctor_set(v___x_1101_, 1, v_value_1099_);
v___x_1102_ = lean_array_push(v_x_1096_, v___x_1101_);
v_x_1096_ = v___x_1102_;
v_x_1097_ = v_tail_1100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1104_, v_x_1105_);
lean_dec(v_x_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object* v_as_1107_, size_t v_i_1108_, size_t v_stop_1109_, lean_object* v_b_1110_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_usize_dec_eq(v_i_1108_, v_stop_1109_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; 
v___x_1112_ = lean_array_uget_borrowed(v_as_1107_, v_i_1108_);
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_b_1110_, v___x_1112_);
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_add(v_i_1108_, v___x_1114_);
v_i_1108_ = v___x_1115_;
v_b_1110_ = v___x_1113_;
goto _start;
}
else
{
return v_b_1110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object* v_as_1117_, lean_object* v_i_1118_, lean_object* v_stop_1119_, lean_object* v_b_1120_){
_start:
{
size_t v_i_boxed_1121_; size_t v_stop_boxed_1122_; lean_object* v_res_1123_; 
v_i_boxed_1121_ = lean_unbox_usize(v_i_1118_);
lean_dec(v_i_1118_);
v_stop_boxed_1122_ = lean_unbox_usize(v_stop_1119_);
lean_dec(v_stop_1119_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1117_, v_i_boxed_1121_, v_stop_boxed_1122_, v_b_1120_);
lean_dec_ref(v_as_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object* v_results_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_size_1143_; lean_object* v_buckets_1144_; lean_object* v___x_1145_; lean_object* v_key_1146_; lean_object* v___y_1148_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_size_1143_ = lean_ctor_get(v_results_1124_, 0);
v_buckets_1144_ = lean_ctor_get(v_results_1124_, 1);
v___x_1145_ = lean_unsigned_to_nat(0u);
v_key_1146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v___x_1173_ = lean_mk_empty_array_with_capacity(v_size_1143_);
v___x_1174_ = lean_array_get_size(v_buckets_1144_);
v___x_1175_ = lean_nat_dec_lt(v___x_1145_, v___x_1174_);
if (v___x_1175_ == 0)
{
v___y_1148_ = v___x_1173_;
goto v___jp_1147_;
}
else
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_le(v___x_1174_, v___x_1174_);
if (v___x_1176_ == 0)
{
if (v___x_1175_ == 0)
{
v___y_1148_ = v___x_1173_;
goto v___jp_1147_;
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1174_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1144_, v___x_1177_, v___x_1178_, v___x_1173_);
v___y_1148_ = v___x_1179_;
goto v___jp_1147_;
}
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1174_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1144_, v___x_1180_, v___x_1181_, v___x_1173_);
v___y_1148_ = v___x_1182_;
goto v___jp_1147_;
}
}
v___jp_1128_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v___y_1131_, v___y_1132_, v___y_1129_, v___y_1130_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
v___jp_1136_:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_nat_dec_le(v___y_1141_, v___y_1138_);
if (v___x_1142_ == 0)
{
lean_dec(v___y_1138_);
lean_inc(v___y_1141_);
v___y_1129_ = v___y_1137_;
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1139_;
v___y_1132_ = v___y_1140_;
v___y_1133_ = v___y_1141_;
goto v___jp_1128_;
}
else
{
v___y_1129_ = v___y_1137_;
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1139_;
v___y_1132_ = v___y_1140_;
v___y_1133_ = v___y_1138_;
goto v___jp_1128_;
}
}
v___jp_1147_:
{
size_t v_sz_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v_sz_1149_ = lean_array_size(v___y_1148_);
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v___y_1148_, v_sz_1149_, v___x_1150_, v_key_1146_, v_a_1125_, v_a_1126_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1164_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1164_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1164_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_array_get_size(v___y_1148_);
v___x_1157_ = lean_nat_dec_eq(v___x_1156_, v___x_1145_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
lean_del_object(v___x_1154_);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_sub(v___x_1156_, v___x_1158_);
v___x_1160_ = lean_nat_dec_le(v___x_1145_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_inc(v___x_1159_);
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___x_1159_;
v___y_1139_ = v_a_1152_;
v___y_1140_ = v___x_1156_;
v___y_1141_ = v___x_1159_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___x_1159_;
v___y_1139_ = v_a_1152_;
v___y_1140_ = v___x_1156_;
v___y_1141_ = v___x_1145_;
goto v___jp_1136_;
}
}
else
{
lean_object* v___x_1162_; 
lean_dec(v_a_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___y_1148_);
v___x_1162_ = v___x_1154_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___y_1148_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v___y_1148_);
v_a_1165_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1151_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1151_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object* v_results_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec_ref(v_results_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object* v_00_u03b1_1188_, lean_object* v_results_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1189_, v_a_1190_, v_a_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_results_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Linter_EnvLinter_sortResults(v_00_u03b1_1194_, v_results_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec_ref(v_results_1195_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object* v_declName_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1200_, v___y_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object* v_declName_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(v_declName_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object* v_declName_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1210_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object* v_declName_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(v_declName_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object* v_00_u03b1_1220_, lean_object* v_as_1221_, size_t v_sz_1222_, size_t v_i_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1221_, v_sz_1222_, v_i_1223_, v_b_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_as_1230_, lean_object* v_sz_1231_, lean_object* v_i_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1231_);
lean_dec(v_sz_1231_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(v_00_u03b1_1229_, v_as_1230_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v_as_1230_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object* v_00_u03b2_1240_, lean_object* v_m_1241_, lean_object* v_a_1242_, lean_object* v_fallback_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1241_, v_a_1242_, v_fallback_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_, lean_object* v_fallback_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(v_00_u03b2_1245_, v_m_1246_, v_a_1247_, v_fallback_1248_);
lean_dec(v_fallback_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_m_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object* v_00_u03b1_1250_, lean_object* v_a_1251_, lean_object* v_n_1252_, lean_object* v_as_1253_, lean_object* v_lo_1254_, lean_object* v_hi_1255_, lean_object* v_w_1256_, lean_object* v_hlo_1257_, lean_object* v_hhi_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1251_, v_n_1252_, v_as_1253_, v_lo_1254_, v_hi_1255_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_a_1261_, lean_object* v_n_1262_, lean_object* v_as_1263_, lean_object* v_lo_1264_, lean_object* v_hi_1265_, lean_object* v_w_1266_, lean_object* v_hlo_1267_, lean_object* v_hhi_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(v_00_u03b1_1260_, v_a_1261_, v_n_1262_, v_as_1263_, v_lo_1264_, v_hi_1265_, v_w_1266_, v_hlo_1267_, v_hhi_1268_);
lean_dec(v_hi_1265_);
lean_dec(v_n_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object* v_00_u03b1_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1271_, v_x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(v_00_u03b1_1274_, v_x_1275_, v_x_1276_);
lean_dec(v_x_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object* v_00_u03b1_1278_, lean_object* v_as_1279_, size_t v_i_1280_, size_t v_stop_1281_, lean_object* v_b_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1279_, v_i_1280_, v_stop_1281_, v_b_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_as_1285_, lean_object* v_i_1286_, lean_object* v_stop_1287_, lean_object* v_b_1288_){
_start:
{
size_t v_i_boxed_1289_; size_t v_stop_boxed_1290_; lean_object* v_res_1291_; 
v_i_boxed_1289_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_stop_boxed_1290_ = lean_unbox_usize(v_stop_1287_);
lean_dec(v_stop_1287_);
v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(v_00_u03b1_1284_, v_as_1285_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1288_);
lean_dec_ref(v_as_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object* v_00_u03b2_1292_, lean_object* v_a_1293_, lean_object* v_fallback_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1293_, v_fallback_1294_, v_x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_a_1298_, lean_object* v_fallback_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(v_00_u03b2_1297_, v_a_1298_, v_fallback_1299_, v_x_1300_);
lean_dec(v_x_1300_);
lean_dec(v_fallback_1299_);
lean_dec(v_a_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object* v_00_u03b1_1302_, lean_object* v_a_1303_, lean_object* v_n_1304_, lean_object* v_lo_1305_, lean_object* v_hi_1306_, lean_object* v_hhi_1307_, lean_object* v_pivot_1308_, lean_object* v_as_1309_, lean_object* v_i_1310_, lean_object* v_k_1311_, lean_object* v_ilo_1312_, lean_object* v_ik_1313_, lean_object* v_w_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1303_, v_hi_1306_, v_pivot_1308_, v_as_1309_, v_i_1310_, v_k_1311_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_a_1317_, lean_object* v_n_1318_, lean_object* v_lo_1319_, lean_object* v_hi_1320_, lean_object* v_hhi_1321_, lean_object* v_pivot_1322_, lean_object* v_as_1323_, lean_object* v_i_1324_, lean_object* v_k_1325_, lean_object* v_ilo_1326_, lean_object* v_ik_1327_, lean_object* v_w_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(v_00_u03b1_1316_, v_a_1317_, v_n_1318_, v_lo_1319_, v_hi_1320_, v_hhi_1321_, v_pivot_1322_, v_as_1323_, v_i_1324_, v_k_1325_, v_ilo_1326_, v_ik_1327_, v_w_1328_);
lean_dec_ref(v_pivot_1322_);
lean_dec(v_hi_1320_);
lean_dec(v_lo_1319_);
lean_dec(v_n_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_ctor_set(v___x_1332_, 2, v___x_1331_);
lean_ctor_set(v___x_1332_, 3, v___x_1331_);
lean_ctor_set(v___x_1332_, 4, v___x_1330_);
lean_ctor_set(v___x_1332_, 5, v___x_1330_);
lean_ctor_set(v___x_1332_, 6, v___x_1330_);
lean_ctor_set(v___x_1332_, 7, v___x_1330_);
lean_ctor_set(v___x_1332_, 8, v___x_1330_);
lean_ctor_set(v___x_1332_, 9, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(32u);
v___x_1334_ = lean_mk_empty_array_with_capacity(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2(void){
_start:
{
size_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = ((size_t)5ULL);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_unsigned_to_nat(32u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1);
v___x_1341_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v___x_1337_);
lean_ctor_set(v___x_1341_, 3, v___x_1337_);
lean_ctor_set_usize(v___x_1341_, 4, v___x_1336_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_box(1);
v___x_1343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2);
v___x_1344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
lean_ctor_set(v___x_1345_, 2, v___x_1342_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object* v_msgData_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v_env_1351_; lean_object* v_options_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1350_ = lean_st_ref_get(v___y_1348_);
v_env_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_ref(v_env_1351_);
lean_dec(v___x_1350_);
v_options_1352_ = lean_ctor_get(v___y_1347_, 2);
v___x_1353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1354_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
lean_inc_ref(v_options_1352_);
v___x_1355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1355_, 0, v_env_1351_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
lean_ctor_set(v___x_1355_, 2, v___x_1354_);
lean_ctor_set(v___x_1355_, 3, v_options_1352_);
v___x_1356_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v_msgData_1346_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object* v_msgData_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msgData_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
if (lean_obj_tag(v_a_1363_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = l_List_reverse___redArg(v_a_1364_);
return v___x_1365_;
}
else
{
lean_object* v_head_1366_; lean_object* v_tail_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1376_; 
v_head_1366_ = lean_ctor_get(v_a_1363_, 0);
v_tail_1367_ = lean_ctor_get(v_a_1363_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_a_1363_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1369_ = v_a_1363_;
v_isShared_1370_ = v_isSharedCheck_1376_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_tail_1367_);
lean_inc(v_head_1366_);
lean_dec(v_a_1363_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1376_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l_Lean_mkLevelParam(v_head_1366_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_a_1364_);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_a_1364_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v_a_1363_ = v_tail_1367_;
v_a_1364_ = v___x_1373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_ref_1381_; lean_object* v___x_1382_; lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_ref_1381_ = lean_ctor_get(v___y_1378_, 5);
v___x_1382_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msg_1377_, v___y_1378_, v___y_1379_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_inc(v_ref_1381_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_ref_1381_);
lean_ctor_set(v___x_1387_, 1, v_a_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_fileName_1402_; lean_object* v_fileMap_1403_; lean_object* v_options_1404_; lean_object* v_currRecDepth_1405_; lean_object* v_maxRecDepth_1406_; lean_object* v_ref_1407_; lean_object* v_currNamespace_1408_; lean_object* v_openDecls_1409_; lean_object* v_initHeartbeats_1410_; lean_object* v_maxHeartbeats_1411_; lean_object* v_quotContext_1412_; lean_object* v_currMacroScope_1413_; uint8_t v_diag_1414_; lean_object* v_cancelTk_x3f_1415_; uint8_t v_suppressElabErrors_1416_; lean_object* v_inheritedTraceOptions_1417_; lean_object* v_ref_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_fileName_1402_ = lean_ctor_get(v___y_1399_, 0);
v_fileMap_1403_ = lean_ctor_get(v___y_1399_, 1);
v_options_1404_ = lean_ctor_get(v___y_1399_, 2);
v_currRecDepth_1405_ = lean_ctor_get(v___y_1399_, 3);
v_maxRecDepth_1406_ = lean_ctor_get(v___y_1399_, 4);
v_ref_1407_ = lean_ctor_get(v___y_1399_, 5);
v_currNamespace_1408_ = lean_ctor_get(v___y_1399_, 6);
v_openDecls_1409_ = lean_ctor_get(v___y_1399_, 7);
v_initHeartbeats_1410_ = lean_ctor_get(v___y_1399_, 8);
v_maxHeartbeats_1411_ = lean_ctor_get(v___y_1399_, 9);
v_quotContext_1412_ = lean_ctor_get(v___y_1399_, 10);
v_currMacroScope_1413_ = lean_ctor_get(v___y_1399_, 11);
v_diag_1414_ = lean_ctor_get_uint8(v___y_1399_, sizeof(void*)*14);
v_cancelTk_x3f_1415_ = lean_ctor_get(v___y_1399_, 12);
v_suppressElabErrors_1416_ = lean_ctor_get_uint8(v___y_1399_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1417_ = lean_ctor_get(v___y_1399_, 13);
v_ref_1418_ = l_Lean_replaceRef(v_ref_1397_, v_ref_1407_);
lean_inc_ref(v_inheritedTraceOptions_1417_);
lean_inc(v_cancelTk_x3f_1415_);
lean_inc(v_currMacroScope_1413_);
lean_inc(v_quotContext_1412_);
lean_inc(v_maxHeartbeats_1411_);
lean_inc(v_initHeartbeats_1410_);
lean_inc(v_openDecls_1409_);
lean_inc(v_currNamespace_1408_);
lean_inc(v_maxRecDepth_1406_);
lean_inc(v_currRecDepth_1405_);
lean_inc_ref(v_options_1404_);
lean_inc_ref(v_fileMap_1403_);
lean_inc_ref(v_fileName_1402_);
v___x_1419_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1419_, 0, v_fileName_1402_);
lean_ctor_set(v___x_1419_, 1, v_fileMap_1403_);
lean_ctor_set(v___x_1419_, 2, v_options_1404_);
lean_ctor_set(v___x_1419_, 3, v_currRecDepth_1405_);
lean_ctor_set(v___x_1419_, 4, v_maxRecDepth_1406_);
lean_ctor_set(v___x_1419_, 5, v_ref_1418_);
lean_ctor_set(v___x_1419_, 6, v_currNamespace_1408_);
lean_ctor_set(v___x_1419_, 7, v_openDecls_1409_);
lean_ctor_set(v___x_1419_, 8, v_initHeartbeats_1410_);
lean_ctor_set(v___x_1419_, 9, v_maxHeartbeats_1411_);
lean_ctor_set(v___x_1419_, 10, v_quotContext_1412_);
lean_ctor_set(v___x_1419_, 11, v_currMacroScope_1413_);
lean_ctor_set(v___x_1419_, 12, v_cancelTk_x3f_1415_);
lean_ctor_set(v___x_1419_, 13, v_inheritedTraceOptions_1417_);
lean_ctor_set_uint8(v___x_1419_, sizeof(void*)*14, v_diag_1414_);
lean_ctor_set_uint8(v___x_1419_, sizeof(void*)*14 + 1, v_suppressElabErrors_1416_);
v___x_1420_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1398_, v___x_1419_, v___y_1400_);
lean_dec_ref_known(v___x_1419_, 14);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1421_, lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1421_, v_msg_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v_ref_1421_);
return v_res_1426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1441_ = l_Lean_stringToMessageData(v___x_1440_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1444_ = l_Lean_stringToMessageData(v___x_1443_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1447_ = l_Lean_stringToMessageData(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1448_, lean_object* v_declHint_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v_env_1453_; uint8_t v___y_1455_; uint8_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1452_ = lean_st_ref_get(v___y_1450_);
v_env_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_env_1453_);
lean_dec(v___x_1452_);
v___x_1511_ = l_Lean_Name_isAnonymous(v_declHint_1449_);
v___x_1512_ = lean_bool_not(v___x_1511_);
if (v___x_1512_ == 0)
{
v___y_1455_ = v___x_1512_;
goto v___jp_1454_;
}
else
{
uint8_t v_isExporting_1513_; 
v_isExporting_1513_ = lean_ctor_get_uint8(v_env_1453_, sizeof(void*)*8);
v___y_1455_ = v_isExporting_1513_;
goto v___jp_1454_;
}
v___jp_1454_:
{
if (v___y_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref(v_env_1453_);
lean_dec(v_declHint_1449_);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_msg_1448_);
return v___x_1456_;
}
else
{
uint8_t v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = 0;
lean_inc_ref(v_env_1453_);
v___x_1458_ = l_Lean_Environment_setExporting(v_env_1453_, v___x_1457_);
lean_inc(v_declHint_1449_);
lean_inc_ref(v___x_1458_);
v___x_1459_ = l_Lean_Environment_contains(v___x_1458_, v_declHint_1449_, v___y_1455_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_env_1453_);
lean_dec(v_declHint_1449_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_msg_1448_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_c_1466_; lean_object* v___x_1467_; 
v___x_1461_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1462_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
v___x_1463_ = l_Lean_Options_empty;
v___x_1464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1458_);
lean_ctor_set(v___x_1464_, 1, v___x_1461_);
lean_ctor_set(v___x_1464_, 2, v___x_1462_);
lean_ctor_set(v___x_1464_, 3, v___x_1463_);
lean_inc(v_declHint_1449_);
v___x_1465_ = l_Lean_MessageData_ofConstName(v_declHint_1449_, v___x_1457_);
v_c_1466_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1466_, 0, v___x_1464_);
lean_ctor_set(v_c_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1453_, v_declHint_1449_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_env_1453_);
lean_dec(v_declHint_1449_);
v___x_1468_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_c_1466_);
v___x_1470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_MessageData_note(v___x_1471_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_msg_1448_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
else
{
lean_object* v_val_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1510_; 
v_val_1475_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1477_ = v___x_1467_;
v_isShared_1478_ = v_isSharedCheck_1510_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_val_1475_);
lean_dec(v___x_1467_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1510_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_mod_1482_; uint8_t v___x_1483_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = l_Lean_Environment_header(v_env_1453_);
lean_dec_ref(v_env_1453_);
v___x_1481_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1480_);
v_mod_1482_ = lean_array_get(v___x_1479_, v___x_1481_, v_val_1475_);
lean_dec(v_val_1475_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = l_Lean_isPrivateName(v_declHint_1449_);
lean_dec(v_declHint_1449_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_c_1466_);
v___x_1486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_MessageData_ofName(v_mod_1482_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = l_Lean_MessageData_note(v___x_1491_);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_msg_1448_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1493_);
v___x_1495_ = v___x_1477_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_c_1466_);
v___x_1499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = l_Lean_MessageData_ofName(v_mod_1482_);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_MessageData_note(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_msg_1448_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1506_);
v___x_1508_ = v___x_1477_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1514_, v_declHint_1515_, v___y_1516_);
lean_dec(v___y_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_1519_, lean_object* v_declHint_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1534_; 
v___x_1524_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1519_, v_declHint_1520_, v___y_1522_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1529_ = l_Lean_unknownIdentifierMessageTag;
v___x_1530_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_a_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_1535_, lean_object* v_declHint_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1535_, v_declHint_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1541_, lean_object* v_msg_1542_, lean_object* v_declHint_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v_a_1548_; lean_object* v___x_1549_; 
v___x_1547_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1542_, v_declHint_1543_, v___y_1544_, v___y_1545_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1541_, v_a_1548_, v___y_1544_, v___y_1545_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1550_, lean_object* v_msg_1551_, lean_object* v_declHint_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1550_, v_msg_1551_, v_declHint_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v_ref_1550_);
return v_res_1556_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1563_, lean_object* v_constName_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1568_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1569_ = 0;
lean_inc(v_constName_1564_);
v___x_1570_ = l_Lean_MessageData_ofConstName(v_constName_1564_, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1568_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1563_, v___x_1573_, v_constName_1564_, v___y_1565_, v___y_1566_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1575_, lean_object* v_constName_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1575_, v_constName_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v_ref_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_ref_1585_; lean_object* v___x_1586_; 
v_ref_1585_ = lean_ctor_get(v___y_1582_, 5);
v___x_1586_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1585_, v_constName_1581_, v___y_1582_, v___y_1583_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object* v_constName_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v_env_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1596_ = lean_st_ref_get(v___y_1594_);
v_env_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_env_1597_);
lean_dec(v___x_1596_);
v___x_1598_ = 0;
lean_inc(v_constName_1592_);
v___x_1599_ = l_Lean_Environment_findConstVal_x3f(v_env_1597_, v_constName_1592_, v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1592_, v___y_1593_, v___y_1594_);
return v___x_1600_;
}
else
{
lean_object* v_val_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_constName_1592_);
v_val_1601_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1599_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_val_1601_);
lean_dec(v___x_1599_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_val_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object* v_constName_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object* v_constName_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
lean_inc(v_constName_1614_);
v___x_1618_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1630_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1630_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1630_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_levelParams_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v_levelParams_1623_ = lean_ctor_get(v_a_1619_, 1);
lean_inc(v_levelParams_1623_);
lean_dec(v_a_1619_);
v___x_1624_ = lean_box(0);
v___x_1625_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(v_levelParams_1623_, v___x_1624_);
v___x_1626_ = l_Lean_mkConst(v_constName_1614_, v___x_1625_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1626_);
v___x_1628_ = v___x_1621_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_constName_1614_);
v_a_1631_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1618_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1618_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object* v_constName_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_constName_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__0));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__3(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__2));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__5(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__4));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__7(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__6));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__9(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__8));
v___x_1658_ = l_Lean_stringToMessageData(v___x_1657_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__11(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__10));
v___x_1661_ = l_Lean_stringToMessageData(v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object* v_declName_1662_, lean_object* v_warning_1663_, uint8_t v_useErrorFormat_1664_, lean_object* v_filePath_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___y_1670_; lean_object* v___y_1671_; 
if (v_useErrorFormat_1664_ == 0)
{
lean_dec_ref(v_filePath_1665_);
v___y_1670_ = v_a_1666_;
v___y_1671_ = v_a_1667_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1691_; 
lean_inc(v_declName_1662_);
v___x_1691_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1662_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
if (lean_obj_tag(v_a_1692_) == 1)
{
lean_object* v_val_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1749_; 
v_val_1693_ = lean_ctor_get(v_a_1692_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_a_1692_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1695_ = v_a_1692_;
v_isShared_1696_ = v_isSharedCheck_1749_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_val_1693_);
lean_dec(v_a_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1749_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1662_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_range_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1739_; 
v_range_1698_ = lean_ctor_get(v_val_1693_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_val_1693_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_val_1693_, 1);
lean_dec(v_unused_1740_);
v___x_1700_ = v_val_1693_;
v_isShared_1701_ = v_isSharedCheck_1739_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_range_1698_);
lean_dec(v_val_1693_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1739_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_pos_1702_; lean_object* v_a_1703_; lean_object* v_line_1704_; lean_object* v_column_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1738_; 
v_pos_1702_ = lean_ctor_get(v_range_1698_, 0);
lean_inc_ref(v_pos_1702_);
lean_dec_ref(v_range_1698_);
v_a_1703_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1697_, 1);
v_line_1704_ = lean_ctor_get(v_pos_1702_, 0);
v_column_1705_ = lean_ctor_get(v_pos_1702_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_pos_1702_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1707_ = v_pos_1702_;
v_isShared_1708_ = v_isSharedCheck_1738_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_column_1705_);
lean_inc(v_line_1704_);
lean_dec(v_pos_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1738_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 3);
lean_ctor_set(v___x_1695_, 0, v_filePath_1665_);
v___x_1710_ = v___x_1695_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_filePath_1665_);
v___x_1710_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = l_Lean_MessageData_ofFormat(v___x_1710_);
v___x_1712_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__7, &l_Lean_Linter_EnvLinter_printWarning___closed__7_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__7);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 7);
lean_ctor_set(v___x_1707_, 1, v___x_1712_);
lean_ctor_set(v___x_1707_, 0, v___x_1711_);
v___x_1714_ = v___x_1707_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1715_ = l_Nat_reprFast(v_line_1704_);
v___x_1716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 7);
lean_ctor_set(v___x_1700_, 1, v___x_1717_);
lean_ctor_set(v___x_1700_, 0, v___x_1714_);
v___x_1719_ = v___x_1700_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___x_1712_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_add(v_column_1705_, v___x_1721_);
lean_dec(v_column_1705_);
v___x_1723_ = l_Nat_reprFast(v___x_1722_);
v___x_1724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___x_1725_ = l_Lean_MessageData_ofFormat(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1720_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__9, &l_Lean_Linter_EnvLinter_printWarning___closed__9_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__9);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_MessageData_ofExpr(v_a_1703_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__11, &l_Lean_Linter_EnvLinter_printWarning___closed__11_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__11);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_warning_1663_);
v___x_1734_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1733_, v_a_1666_, v_a_1667_);
return v___x_1734_;
}
}
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_del_object(v___x_1695_);
lean_dec(v_val_1693_);
lean_dec_ref(v_filePath_1665_);
lean_dec_ref(v_warning_1663_);
v_a_1741_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1697_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1697_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
else
{
lean_dec(v_a_1692_);
lean_dec_ref(v_filePath_1665_);
v___y_1670_ = v_a_1666_;
v___y_1671_ = v_a_1667_;
goto v___jp_1669_;
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_filePath_1665_);
lean_dec_ref(v_warning_1663_);
lean_dec(v_declName_1662_);
v_a_1750_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1691_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1691_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
v___jp_1669_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1662_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__1, &l_Lean_Linter_EnvLinter_printWarning___closed__1_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__1);
v___x_1675_ = l_Lean_MessageData_ofExpr(v_a_1673_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__3, &l_Lean_Linter_EnvLinter_printWarning___closed__3_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__3);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v_warning_1663_);
v___x_1680_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1681_, v___y_1670_, v___y_1671_);
return v___x_1682_;
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_warning_1663_);
v_a_1683_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1672_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1672_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object* v_declName_1758_, lean_object* v_warning_1759_, lean_object* v_useErrorFormat_1760_, lean_object* v_filePath_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v_useErrorFormat_boxed_1765_; lean_object* v_res_1766_; 
v_useErrorFormat_boxed_1765_ = lean_unbox(v_useErrorFormat_1760_);
v_res_1766_ = l_Lean_Linter_EnvLinter_printWarning(v_declName_1758_, v_warning_1759_, v_useErrorFormat_boxed_1765_, v_filePath_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1767_, lean_object* v_constName_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1768_, v___y_1769_, v___y_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_constName_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(v_00_u03b1_1773_, v_constName_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1779_, lean_object* v_ref_1780_, lean_object* v_constName_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1780_, v_constName_1781_, v___y_1782_, v___y_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1786_, lean_object* v_ref_1787_, lean_object* v_constName_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1786_, v_ref_1787_, v_constName_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v_ref_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1793_, lean_object* v_ref_1794_, lean_object* v_msg_1795_, lean_object* v_declHint_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1794_, v_msg_1795_, v_declHint_1796_, v___y_1797_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_ref_1802_, lean_object* v_msg_1803_, lean_object* v_declHint_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1801_, v_ref_1802_, v_msg_1803_, v_declHint_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v_ref_1802_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_1809_, lean_object* v_declHint_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1809_, v_declHint_1810_, v___y_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_1815_, lean_object* v_declHint_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_1815_, v_declHint_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1821_, lean_object* v_ref_1822_, lean_object* v_msg_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1822_, v_msg_1823_, v___y_1824_, v___y_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_ref_1829_, lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1828_, v_ref_1829_, v_msg_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v_ref_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1836_, v___y_1837_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_1841_, v_msg_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t v_useErrorFormat_1847_, lean_object* v_filePath_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_bs_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v_filePath_1848_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_bs_1851_);
return v___x_1856_;
}
else
{
lean_object* v_v_1857_; lean_object* v_fst_1858_; lean_object* v_snd_1859_; lean_object* v___x_1860_; 
v_v_1857_ = lean_array_uget_borrowed(v_bs_1851_, v_i_1850_);
v_fst_1858_ = lean_ctor_get(v_v_1857_, 0);
v_snd_1859_ = lean_ctor_get(v_v_1857_, 1);
lean_inc_ref(v_filePath_1848_);
lean_inc(v_snd_1859_);
lean_inc(v_fst_1858_);
v___x_1860_ = l_Lean_Linter_EnvLinter_printWarning(v_fst_1858_, v_snd_1859_, v_useErrorFormat_1847_, v_filePath_1848_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; lean_object* v_bs_x27_1863_; size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v___x_1862_ = lean_unsigned_to_nat(0u);
v_bs_x27_1863_ = lean_array_uset(v_bs_1851_, v_i_1850_, v___x_1862_);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_add(v_i_1850_, v___x_1864_);
v___x_1866_ = lean_array_uset(v_bs_x27_1863_, v_i_1850_, v_a_1861_);
v_i_1850_ = v___x_1865_;
v_bs_1851_ = v___x_1866_;
goto _start;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_bs_1851_);
lean_dec_ref(v_filePath_1848_);
v_a_1868_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1860_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1860_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object* v_useErrorFormat_1876_, lean_object* v_filePath_1877_, lean_object* v_sz_1878_, lean_object* v_i_1879_, lean_object* v_bs_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
uint8_t v_useErrorFormat_boxed_1884_; size_t v_sz_boxed_1885_; size_t v_i_boxed_1886_; lean_object* v_res_1887_; 
v_useErrorFormat_boxed_1884_ = lean_unbox(v_useErrorFormat_1876_);
v_sz_boxed_1885_ = lean_unbox_usize(v_sz_1878_);
lean_dec(v_sz_1878_);
v_i_boxed_1886_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_res_1887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_boxed_1884_, v_filePath_1877_, v_sz_boxed_1885_, v_i_boxed_1886_, v_bs_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1887_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_box(1);
v___x_1889_ = l_Lean_MessageData_ofFormat(v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object* v_results_1890_, lean_object* v_filePath_1891_, uint8_t v_useErrorFormat_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1890_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; size_t v_sz_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v_sz_1898_ = lean_array_size(v_a_1897_);
v___x_1899_ = ((size_t)0ULL);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_1892_, v_filePath_1891_, v_sz_1898_, v___x_1899_, v_a_1897_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1911_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1905_ = lean_array_to_list(v_a_1901_);
v___x_1906_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_1907_ = l_Lean_MessageData_joinSep(v___x_1905_, v___x_1906_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1907_);
v___x_1909_ = v___x_1903_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1900_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1900_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v_filePath_1891_);
v_a_1920_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1896_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1896_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object* v_results_1928_, lean_object* v_filePath_1929_, lean_object* v_useErrorFormat_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_useErrorFormat_boxed_1934_; lean_object* v_res_1935_; 
v_useErrorFormat_boxed_1934_ = lean_unbox(v_useErrorFormat_1930_);
v_res_1935_ = l_Lean_Linter_EnvLinter_printWarnings(v_results_1928_, v_filePath_1929_, v_useErrorFormat_boxed_1934_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec_ref(v_results_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
return v_x_1936_;
}
else
{
lean_object* v_key_1938_; lean_object* v_value_1939_; lean_object* v_tail_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_key_1938_ = lean_ctor_get(v_x_1937_, 0);
v_value_1939_ = lean_ctor_get(v_x_1937_, 1);
v_tail_1940_ = lean_ctor_get(v_x_1937_, 2);
lean_inc(v_value_1939_);
lean_inc(v_key_1938_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_key_1938_);
lean_ctor_set(v___x_1941_, 1, v_value_1939_);
v___x_1942_ = lean_array_push(v_x_1936_, v___x_1941_);
v_x_1936_ = v___x_1942_;
v_x_1937_ = v_tail_1940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_x_1944_, v_x_1945_);
lean_dec(v_x_1945_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object* v_as_1947_, size_t v_i_1948_, size_t v_stop_1949_, lean_object* v_b_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_usize_dec_eq(v_i_1948_, v_stop_1949_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; 
v___x_1952_ = lean_array_uget_borrowed(v_as_1947_, v_i_1948_);
v___x_1953_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_b_1950_, v___x_1952_);
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_add(v_i_1948_, v___x_1954_);
v_i_1948_ = v___x_1955_;
v_b_1950_ = v___x_1953_;
goto _start;
}
else
{
return v_b_1950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object* v_as_1957_, lean_object* v_i_1958_, lean_object* v_stop_1959_, lean_object* v_b_1960_){
_start:
{
size_t v_i_boxed_1961_; size_t v_stop_boxed_1962_; lean_object* v_res_1963_; 
v_i_boxed_1961_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_stop_boxed_1962_ = lean_unbox_usize(v_stop_1959_);
lean_dec(v_stop_1959_);
v_res_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_as_1957_, v_i_boxed_1961_, v_stop_boxed_1962_, v_b_1960_);
lean_dec_ref(v_as_1957_);
return v_res_1963_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t v_useErrorFormat_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
if (lean_obj_tag(v_x_1971_) == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = l_List_reverse___redArg(v_x_1972_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
else
{
lean_object* v_head_1978_; lean_object* v_tail_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2022_; 
v_head_1978_ = lean_ctor_get(v_x_1971_, 0);
v_tail_1979_ = lean_ctor_get(v_x_1971_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1971_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1981_ = v_x_1971_;
v_isShared_1982_ = v_isSharedCheck_2022_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_tail_1979_);
lean_inc(v_head_1978_);
lean_dec(v_x_1971_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2022_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v_a_1984_; lean_object* v_snd_1989_; lean_object* v_fst_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2021_; 
v_snd_1989_ = lean_ctor_get(v_head_1978_, 1);
v_fst_1990_ = lean_ctor_get(v_head_1978_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_head_1978_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1992_ = v_head_1978_;
v_isShared_1993_ = v_isSharedCheck_2021_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_snd_1989_);
lean_inc(v_fst_1990_);
lean_dec(v_head_1978_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2021_;
goto v_resetjp_1991_;
}
v___jp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 1, v_x_1972_);
lean_ctor_set(v___x_1981_, 0, v_a_1984_);
v___x_1986_ = v___x_1981_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1984_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_x_1972_);
v___x_1986_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v_x_1971_ = v_tail_1979_;
v_x_1972_ = v___x_1986_;
goto _start;
}
}
v_resetjp_1991_:
{
lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2020_; 
v_fst_1994_ = lean_ctor_get(v_snd_1989_, 0);
v_snd_1995_ = lean_ctor_get(v_snd_1989_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_snd_1989_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1997_ = v_snd_1989_;
v_isShared_1998_ = v_isSharedCheck_2020_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1995_);
lean_inc(v_fst_1994_);
lean_dec(v_snd_1989_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2020_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_1995_, v_fst_1994_, v_useErrorFormat_1970_, v___y_1973_, v___y_1974_);
lean_dec(v_snd_1995_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1);
v___x_2002_ = l_Lean_MessageData_ofName(v_fst_1990_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 7);
lean_ctor_set(v___x_1997_, 1, v___x_2002_);
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2004_ = v___x_1997_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 7);
lean_ctor_set(v___x_1992_, 1, v___x_2005_);
lean_ctor_set(v___x_1992_, 0, v___x_2004_);
v___x_2007_ = v___x_1992_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v_a_2000_);
v_a_1984_ = v___x_2008_;
goto v___jp_1983_;
}
}
}
else
{
lean_del_object(v___x_1997_);
lean_del_object(v___x_1992_);
lean_dec(v_fst_1990_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_1999_, 1);
v_a_1984_ = v_a_2011_;
goto v___jp_1983_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_del_object(v___x_1981_);
lean_dec(v_tail_1979_);
lean_dec(v_x_1972_);
v_a_2012_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1999_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1999_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object* v_useErrorFormat_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v_useErrorFormat_boxed_2029_; lean_object* v_res_2030_; 
v_useErrorFormat_boxed_2029_ = lean_unbox(v_useErrorFormat_2023_);
v_res_2030_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_boxed_2029_, v_x_2024_, v_x_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object* v_a_2031_, lean_object* v_x_2032_){
_start:
{
if (lean_obj_tag(v_x_2032_) == 0)
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_box(0);
return v___x_2033_;
}
else
{
lean_object* v_key_2034_; lean_object* v_value_2035_; lean_object* v_tail_2036_; uint8_t v___x_2037_; 
v_key_2034_ = lean_ctor_get(v_x_2032_, 0);
v_value_2035_ = lean_ctor_get(v_x_2032_, 1);
v_tail_2036_ = lean_ctor_get(v_x_2032_, 2);
v___x_2037_ = lean_name_eq(v_key_2034_, v_a_2031_);
if (v___x_2037_ == 0)
{
v_x_2032_ = v_tail_2036_;
goto _start;
}
else
{
lean_object* v___x_2039_; 
lean_inc(v_value_2035_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_value_2035_);
return v___x_2039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object* v_a_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2040_, v_x_2041_);
lean_dec(v_x_2041_);
lean_dec(v_a_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object* v_m_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_buckets_2045_; lean_object* v___x_2046_; uint64_t v___y_2048_; 
v_buckets_2045_ = lean_ctor_get(v_m_2043_, 1);
v___x_2046_ = lean_array_get_size(v_buckets_2045_);
if (lean_obj_tag(v_a_2044_) == 0)
{
uint64_t v___x_2062_; 
v___x_2062_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__8___redArg___closed__0);
v___y_2048_ = v___x_2062_;
goto v___jp_2047_;
}
else
{
uint64_t v_hash_2063_; 
v_hash_2063_ = lean_ctor_get_uint64(v_a_2044_, sizeof(void*)*2);
v___y_2048_ = v_hash_2063_;
goto v___jp_2047_;
}
v___jp_2047_:
{
uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v_fold_2051_; uint64_t v___x_2052_; uint64_t v___x_2053_; uint64_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2049_ = 32ULL;
v___x_2050_ = lean_uint64_shift_right(v___y_2048_, v___x_2049_);
v_fold_2051_ = lean_uint64_xor(v___y_2048_, v___x_2050_);
v___x_2052_ = 16ULL;
v___x_2053_ = lean_uint64_shift_right(v_fold_2051_, v___x_2052_);
v___x_2054_ = lean_uint64_xor(v_fold_2051_, v___x_2053_);
v___x_2055_ = lean_uint64_to_usize(v___x_2054_);
v___x_2056_ = lean_usize_of_nat(v___x_2046_);
v___x_2057_ = ((size_t)1ULL);
v___x_2058_ = lean_usize_sub(v___x_2056_, v___x_2057_);
v___x_2059_ = lean_usize_land(v___x_2055_, v___x_2058_);
v___x_2060_ = lean_array_uget_borrowed(v_buckets_2045_, v___x_2059_);
v___x_2061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2044_, v___x_2060_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object* v_m_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_m_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object* v_key_2067_, lean_object* v_value_2068_, lean_object* v_fp_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v___x_2074_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v___x_2073_, v_key_2067_, v_value_2068_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_fp_2069_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object* v_key_2077_, lean_object* v_value_2078_, lean_object* v_fp_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2077_, v_value_2078_, v_fp_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object* v_constName_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v_env_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2088_ = lean_st_ref_get(v___y_2086_);
v_env_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc_ref(v_env_2089_);
lean_dec(v___x_2088_);
v___x_2090_ = 0;
lean_inc(v_constName_2084_);
v___x_2091_ = l_Lean_Environment_find_x3f(v_env_2089_, v_constName_2084_, v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_2084_, v___y_2085_, v___y_2086_);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_constName_2084_);
v_val_2093_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2091_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_val_2093_);
lean_dec(v___x_2091_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 0);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_val_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object* v_constName_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_constName_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object* v_declName_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
lean_inc(v_declName_2106_);
v___x_2110_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_declName_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2137_; 
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2110_, 0);
lean_dec(v_unused_2138_);
v___x_2112_ = v___x_2110_;
v_isShared_2113_ = v_isSharedCheck_2137_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2137_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v_env_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_st_ref_get(v___y_2108_);
v_env_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_ref(v_env_2115_);
lean_dec(v___x_2114_);
v___x_2116_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2115_, v_declName_2106_);
lean_dec(v_declName_2106_);
lean_dec_ref(v_env_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_box(0);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2117_);
v___x_2119_ = v___x_2112_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_object* v_val_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2136_; 
v_val_2121_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2123_ = v___x_2116_;
v_isShared_2124_ = v_isSharedCheck_2136_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_val_2121_);
lean_dec(v___x_2116_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2136_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v_env_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2125_ = lean_st_ref_get(v___y_2108_);
v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_ref(v_env_2126_);
lean_dec(v___x_2125_);
v___x_2127_ = lean_box(0);
v___x_2128_ = l_Lean_Environment_allImportedModuleNames(v_env_2126_);
lean_dec_ref(v_env_2126_);
v___x_2129_ = lean_array_get(v___x_2127_, v___x_2128_, v_val_2121_);
lean_dec(v_val_2121_);
lean_dec_ref(v___x_2128_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2129_);
v___x_2131_ = v___x_2123_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2131_);
v___x_2133_ = v___x_2112_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_declName_2106_);
v_a_2139_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2110_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2110_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object* v_declName_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_declName_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t v_useErrorFormat_2155_, lean_object* v_sp_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
lean_object* v___x_2162_; 
lean_dec(v_sp_2156_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_x_2157_);
return v___x_2162_;
}
else
{
lean_object* v_key_2163_; lean_object* v_value_2164_; lean_object* v_tail_2165_; lean_object* v___y_2167_; lean_object* v_a_2168_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___x_2175_; 
v_key_2163_ = lean_ctor_get(v_x_2158_, 0);
lean_inc_n(v_key_2163_, 2);
v_value_2164_ = lean_ctor_get(v_x_2158_, 1);
lean_inc(v_value_2164_);
v_tail_2165_ = lean_ctor_get(v_x_2158_, 2);
lean_inc(v_tail_2165_);
lean_dec_ref_known(v_x_2158_, 3);
v___x_2175_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_key_2163_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___y_2179_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = lean_st_ref_get(v___y_2160_);
if (lean_obj_tag(v_a_2176_) == 0)
{
lean_object* v_env_2215_; lean_object* v___x_2216_; 
v_env_2215_ = lean_ctor_get(v___x_2177_, 0);
lean_inc_ref(v_env_2215_);
lean_dec(v___x_2177_);
v___x_2216_ = l_Lean_Environment_mainModule(v_env_2215_);
lean_dec_ref(v_env_2215_);
v___y_2179_ = v___x_2216_;
goto v___jp_2178_;
}
else
{
lean_object* v_val_2217_; 
lean_dec(v___x_2177_);
v_val_2217_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_a_2176_, 1);
v___y_2179_ = v_val_2217_;
goto v___jp_2178_;
}
v___jp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_x_2157_, v___y_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
if (v_useErrorFormat_2155_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2182_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2163_, v_value_2164_, v___x_2181_, v___y_2159_, v___y_2160_);
v___y_2172_ = v___y_2179_;
v___y_2173_ = v___x_2182_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1));
lean_inc(v___y_2179_);
lean_inc(v_sp_2156_);
v___x_2184_ = l_Lean_SearchPath_findWithExt(v_sp_2156_, v___x_2183_, v___y_2179_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
if (lean_obj_tag(v_a_2185_) == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2));
lean_inc(v___y_2179_);
v___x_2187_ = l_Lean_modToFilePath(v___x_2186_, v___y_2179_, v___x_2183_);
v___x_2188_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2163_, v_value_2164_, v___x_2187_, v___y_2159_, v___y_2160_);
v___y_2172_ = v___y_2179_;
v___y_2173_ = v___x_2188_;
goto v___jp_2171_;
}
else
{
lean_object* v_val_2189_; lean_object* v___x_2190_; 
v_val_2189_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v_a_2185_, 1);
v___x_2190_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2163_, v_value_2164_, v_val_2189_, v___y_2159_, v___y_2160_);
v___y_2172_ = v___y_2179_;
v___y_2173_ = v___x_2190_;
goto v___jp_2171_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v___y_2179_);
lean_dec(v_tail_2165_);
lean_dec(v_value_2164_);
lean_dec(v_key_2163_);
lean_dec_ref(v_x_2157_);
lean_dec(v_sp_2156_);
v_a_2191_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2193_ = v___x_2184_;
v_isShared_2194_ = v_isSharedCheck_2203_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2184_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2203_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_ref_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v_ref_2195_ = lean_ctor_get(v___y_2159_, 5);
v___x_2196_ = lean_io_error_to_string(v_a_2191_);
v___x_2197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
v___x_2198_ = l_Lean_MessageData_ofFormat(v___x_2197_);
lean_inc(v_ref_2195_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_ref_2195_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2199_);
v___x_2201_ = v___x_2193_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v_val_2204_; lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_val_2204_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2180_, 1);
v_fst_2205_ = lean_ctor_get(v_val_2204_, 0);
v_snd_2206_ = lean_ctor_get(v_val_2204_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_val_2204_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v_val_2204_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_snd_2206_);
lean_inc(v_fst_2205_);
lean_dec(v_val_2204_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_snd_2206_, v_key_2163_, v_value_2164_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_fst_2205_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
v___y_2167_ = v___y_2179_;
v_a_2168_ = v___x_2212_;
goto v___jp_2166_;
}
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_tail_2165_);
lean_dec(v_value_2164_);
lean_dec(v_key_2163_);
lean_dec_ref(v_x_2157_);
lean_dec(v_sp_2156_);
v_a_2218_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2175_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2175_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
v___jp_2166_:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_x_2157_, v___y_2167_, v_a_2168_);
v_x_2157_ = v___x_2169_;
v_x_2158_ = v_tail_2165_;
goto _start;
}
v___jp_2171_:
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___y_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___y_2173_);
v___y_2167_ = v___y_2172_;
v_a_2168_ = v_a_2174_;
goto v___jp_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object* v_useErrorFormat_2226_, lean_object* v_sp_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_useErrorFormat_boxed_2233_; lean_object* v_res_2234_; 
v_useErrorFormat_boxed_2233_ = lean_unbox(v_useErrorFormat_2226_);
v_res_2234_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_boxed_2233_, v_sp_2227_, v_x_2228_, v_x_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t v_useErrorFormat_2235_, lean_object* v_sp_2236_, lean_object* v_as_2237_, size_t v_i_2238_, size_t v_stop_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_usize_dec_eq(v_i_2238_, v_stop_2239_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_array_uget_borrowed(v_as_2237_, v_i_2238_);
lean_inc(v___x_2245_);
lean_inc(v_sp_2236_);
v___x_2246_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_2235_, v_sp_2236_, v_b_2240_, v___x_2245_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; size_t v___x_2248_; size_t v___x_2249_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = ((size_t)1ULL);
v___x_2249_ = lean_usize_add(v_i_2238_, v___x_2248_);
v_i_2238_ = v___x_2249_;
v_b_2240_ = v_a_2247_;
goto _start;
}
else
{
lean_dec(v_sp_2236_);
return v___x_2246_;
}
}
else
{
lean_object* v___x_2251_; 
lean_dec(v_sp_2236_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_b_2240_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object* v_useErrorFormat_2252_, lean_object* v_sp_2253_, lean_object* v_as_2254_, lean_object* v_i_2255_, lean_object* v_stop_2256_, lean_object* v_b_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_useErrorFormat_boxed_2261_; size_t v_i_boxed_2262_; size_t v_stop_boxed_2263_; lean_object* v_res_2264_; 
v_useErrorFormat_boxed_2261_ = lean_unbox(v_useErrorFormat_2252_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_stop_boxed_2263_ = lean_unbox_usize(v_stop_2256_);
lean_dec(v_stop_2256_);
v_res_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_boxed_2261_, v_sp_2253_, v_as_2254_, v_i_boxed_2262_, v_stop_boxed_2263_, v_b_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_as_2254_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object* v_hi_2265_, lean_object* v_pivot_2266_, lean_object* v_as_2267_, lean_object* v_i_2268_, lean_object* v_k_2269_){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_nat_dec_lt(v_k_2269_, v_hi_2265_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec(v_k_2269_);
lean_dec_ref(v_pivot_2266_);
v___x_2271_ = lean_array_fswap(v_as_2267_, v_i_2268_, v_hi_2265_);
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_i_2268_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; lean_object* v_fst_2274_; lean_object* v_fst_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2273_ = lean_array_fget_borrowed(v_as_2267_, v_k_2269_);
v_fst_2274_ = lean_ctor_get(v___x_2273_, 0);
v_fst_2275_ = lean_ctor_get(v_pivot_2266_, 0);
lean_inc(v_fst_2274_);
v___x_2276_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2274_, v___x_2270_);
lean_inc(v_fst_2275_);
v___x_2277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2275_, v___x_2270_);
v___x_2278_ = lean_string_dec_lt(v___x_2276_, v___x_2277_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = lean_nat_add(v_k_2269_, v___x_2279_);
lean_dec(v_k_2269_);
v_k_2269_ = v___x_2280_;
goto _start;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = lean_array_fswap(v_as_2267_, v_i_2268_, v_k_2269_);
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_nat_add(v_i_2268_, v___x_2283_);
lean_dec(v_i_2268_);
v___x_2285_ = lean_nat_add(v_k_2269_, v___x_2283_);
lean_dec(v_k_2269_);
v_as_2267_ = v___x_2282_;
v_i_2268_ = v___x_2284_;
v_k_2269_ = v___x_2285_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object* v_hi_2287_, lean_object* v_pivot_2288_, lean_object* v_as_2289_, lean_object* v_i_2290_, lean_object* v_k_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2287_, v_pivot_2288_, v_as_2289_, v_i_2290_, v_k_2291_);
lean_dec(v_hi_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t v___x_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
lean_object* v_fst_2296_; lean_object* v_fst_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_fst_2296_ = lean_ctor_get(v_x_2294_, 0);
lean_inc(v_fst_2296_);
lean_dec_ref(v_x_2294_);
v_fst_2297_ = lean_ctor_get(v_x_2295_, 0);
lean_inc(v_fst_2297_);
lean_dec_ref(v_x_2295_);
v___x_2298_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2296_, v___x_2293_);
v___x_2299_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2297_, v___x_2293_);
v___x_2300_ = lean_string_dec_lt(v___x_2298_, v___x_2299_);
lean_dec_ref(v___x_2299_);
lean_dec_ref(v___x_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object* v___x_2301_, lean_object* v_x_2302_, lean_object* v_x_2303_){
_start:
{
uint8_t v___x_5444__boxed_2304_; uint8_t v_res_2305_; lean_object* v_r_2306_; 
v___x_5444__boxed_2304_ = lean_unbox(v___x_2301_);
v_res_2305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_5444__boxed_2304_, v_x_2302_, v_x_2303_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object* v_n_2307_, lean_object* v_as_2308_, lean_object* v_lo_2309_, lean_object* v_hi_2310_){
_start:
{
lean_object* v___y_2312_; uint8_t v___x_2322_; 
v___x_2322_ = lean_nat_dec_lt(v_lo_2309_, v_hi_2310_);
if (v___x_2322_ == 0)
{
lean_dec(v_lo_2309_);
return v_as_2308_;
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_mid_2325_; lean_object* v___y_2327_; lean_object* v___y_2333_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2323_ = lean_nat_add(v_lo_2309_, v_hi_2310_);
v___x_2324_ = lean_unsigned_to_nat(1u);
v_mid_2325_ = lean_nat_shiftr(v___x_2323_, v___x_2324_);
lean_dec(v___x_2323_);
v___x_2338_ = lean_array_fget_borrowed(v_as_2308_, v_mid_2325_);
v___x_2339_ = lean_array_fget_borrowed(v_as_2308_, v_lo_2309_);
lean_inc(v___x_2339_);
lean_inc(v___x_2338_);
v___x_2340_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2322_, v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
v___y_2333_ = v_as_2308_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_array_fswap(v_as_2308_, v_lo_2309_, v_mid_2325_);
v___y_2333_ = v___x_2341_;
goto v___jp_2332_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = lean_array_fget_borrowed(v___y_2327_, v_mid_2325_);
v___x_2329_ = lean_array_fget_borrowed(v___y_2327_, v_hi_2310_);
lean_inc(v___x_2329_);
lean_inc(v___x_2328_);
v___x_2330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2322_, v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec(v_mid_2325_);
v___y_2312_ = v___y_2327_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_array_fswap(v___y_2327_, v_mid_2325_, v_hi_2310_);
lean_dec(v_mid_2325_);
v___y_2312_ = v___x_2331_;
goto v___jp_2311_;
}
}
v___jp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2334_ = lean_array_fget_borrowed(v___y_2333_, v_hi_2310_);
v___x_2335_ = lean_array_fget_borrowed(v___y_2333_, v_lo_2309_);
lean_inc(v___x_2335_);
lean_inc(v___x_2334_);
v___x_2336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2322_, v___x_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
v___y_2327_ = v___y_2333_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_array_fswap(v___y_2333_, v_lo_2309_, v_hi_2310_);
v___y_2327_ = v___x_2337_;
goto v___jp_2326_;
}
}
}
v___jp_2311_:
{
lean_object* v_pivot_2313_; lean_object* v___x_2314_; lean_object* v_fst_2315_; lean_object* v_snd_2316_; uint8_t v___x_2317_; 
v_pivot_2313_ = lean_array_fget(v___y_2312_, v_hi_2310_);
lean_inc_n(v_lo_2309_, 2);
v___x_2314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2310_, v_pivot_2313_, v___y_2312_, v_lo_2309_, v_lo_2309_);
v_fst_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_fst_2315_);
v_snd_2316_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_snd_2316_);
lean_dec_ref(v___x_2314_);
v___x_2317_ = lean_nat_dec_le(v_hi_2310_, v_fst_2315_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2307_, v_snd_2316_, v_lo_2309_, v_fst_2315_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = lean_nat_add(v_fst_2315_, v___x_2319_);
lean_dec(v_fst_2315_);
v_as_2308_ = v___x_2318_;
v_lo_2309_ = v___x_2320_;
goto _start;
}
else
{
lean_dec(v_fst_2315_);
lean_dec(v_lo_2309_);
return v_snd_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object* v_n_2342_, lean_object* v_as_2343_, lean_object* v_lo_2344_, lean_object* v_hi_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2342_, v_as_2343_, v_lo_2344_, v_hi_2345_);
lean_dec(v_hi_2345_);
lean_dec(v_n_2342_);
return v_res_2346_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object* v_results_2349_, uint8_t v_useErrorFormat_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v_size_2408_; lean_object* v_buckets_2409_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v_sp_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; 
if (v_useErrorFormat_2350_ == 0)
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_box(0);
v_sp_2437_ = v___x_2453_;
v___y_2438_ = v_a_2351_;
v___y_2439_ = v_a_2352_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v_sp_2437_ = v_a_2455_;
v___y_2438_ = v_a_2351_;
v___y_2439_ = v_a_2352_;
goto v___jp_2436_;
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2468_; 
v_a_2456_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2458_ = v___x_2454_;
v_isShared_2459_ = v_isSharedCheck_2468_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2468_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_ref_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v_ref_2460_ = lean_ctor_get(v_a_2351_, 5);
v___x_2461_ = lean_io_error_to_string(v_a_2456_);
v___x_2462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
v___x_2463_ = l_Lean_MessageData_ofFormat(v___x_2462_);
lean_inc(v_ref_2460_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_ref_2460_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2464_);
v___x_2466_ = v___x_2458_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
v___jp_2354_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_array_to_list(v___y_2357_);
v___x_2359_ = lean_box(0);
v___x_2360_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_2350_, v___x_2358_, v___x_2359_, v___y_2356_, v___y_2355_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2370_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2370_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2370_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2365_ = lean_obj_once(&l_Lean_Linter_EnvLinter_groupedByFilename___closed__0, &l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once, _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0);
v___x_2366_ = l_Lean_MessageData_joinSep(v_a_2361_, v___x_2365_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2366_);
v___x_2368_ = v___x_2363_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2360_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2360_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
v___jp_2379_:
{
lean_object* v___x_2386_; 
v___x_2386_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v___y_2380_, v___y_2382_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec(v___y_2380_);
v___y_2355_ = v___y_2381_;
v___y_2356_ = v___y_2383_;
v___y_2357_ = v___x_2386_;
goto v___jp_2354_;
}
v___jp_2387_:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_nat_dec_le(v___y_2393_, v___y_2389_);
if (v___x_2394_ == 0)
{
lean_dec(v___y_2389_);
lean_inc(v___y_2393_);
v___y_2380_ = v___y_2388_;
v___y_2381_ = v___y_2391_;
v___y_2382_ = v___y_2390_;
v___y_2383_ = v___y_2392_;
v___y_2384_ = v___y_2393_;
v___y_2385_ = v___y_2393_;
goto v___jp_2379_;
}
else
{
v___y_2380_ = v___y_2388_;
v___y_2381_ = v___y_2391_;
v___y_2382_ = v___y_2390_;
v___y_2383_ = v___y_2392_;
v___y_2384_ = v___y_2393_;
v___y_2385_ = v___y_2389_;
goto v___jp_2379_;
}
}
v___jp_2395_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2399_ = lean_array_get_size(v___y_2398_);
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_nat_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_sub(v___x_2399_, v___x_2402_);
v___x_2404_ = lean_nat_dec_le(v___x_2400_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_inc(v___x_2403_);
v___y_2388_ = v___x_2399_;
v___y_2389_ = v___x_2403_;
v___y_2390_ = v___y_2398_;
v___y_2391_ = v___y_2396_;
v___y_2392_ = v___y_2397_;
v___y_2393_ = v___x_2403_;
goto v___jp_2387_;
}
else
{
v___y_2388_ = v___x_2399_;
v___y_2389_ = v___x_2403_;
v___y_2390_ = v___y_2398_;
v___y_2391_ = v___y_2396_;
v___y_2392_ = v___y_2397_;
v___y_2393_ = v___x_2400_;
goto v___jp_2387_;
}
}
else
{
v___y_2355_ = v___y_2396_;
v___y_2356_ = v___y_2397_;
v___y_2357_ = v___y_2398_;
goto v___jp_2354_;
}
}
v___jp_2405_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2410_ = lean_mk_empty_array_with_capacity(v_size_2408_);
lean_dec(v_size_2408_);
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = lean_array_get_size(v_buckets_2409_);
v___x_2413_ = lean_nat_dec_lt(v___x_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v_buckets_2409_);
v___y_2396_ = v___y_2406_;
v___y_2397_ = v___y_2407_;
v___y_2398_ = v___x_2410_;
goto v___jp_2395_;
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_nat_dec_le(v___x_2412_, v___x_2412_);
if (v___x_2414_ == 0)
{
if (v___x_2413_ == 0)
{
lean_dec_ref(v_buckets_2409_);
v___y_2396_ = v___y_2406_;
v___y_2397_ = v___y_2407_;
v___y_2398_ = v___x_2410_;
goto v___jp_2395_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2412_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2409_, v___x_2415_, v___x_2416_, v___x_2410_);
lean_dec_ref(v_buckets_2409_);
v___y_2396_ = v___y_2406_;
v___y_2397_ = v___y_2407_;
v___y_2398_ = v___x_2417_;
goto v___jp_2395_;
}
}
else
{
size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___x_2412_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2409_, v___x_2418_, v___x_2419_, v___x_2410_);
lean_dec_ref(v_buckets_2409_);
v___y_2396_ = v___y_2406_;
v___y_2397_ = v___y_2407_;
v___y_2398_ = v___x_2420_;
goto v___jp_2395_;
}
}
}
v___jp_2421_:
{
if (lean_obj_tag(v___y_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v_size_2426_; lean_object* v_buckets_2427_; 
v_a_2425_ = lean_ctor_get(v___y_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___y_2424_, 1);
v_size_2426_ = lean_ctor_get(v_a_2425_, 0);
lean_inc(v_size_2426_);
v_buckets_2427_ = lean_ctor_get(v_a_2425_, 1);
lean_inc_ref(v_buckets_2427_);
lean_dec(v_a_2425_);
v___y_2406_ = v___y_2422_;
v___y_2407_ = v___y_2423_;
v_size_2408_ = v_size_2426_;
v_buckets_2409_ = v_buckets_2427_;
goto v___jp_2405_;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v___y_2424_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___y_2424_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___y_2424_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___y_2424_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
v___jp_2436_:
{
lean_object* v_buckets_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v_buckets_2440_ = lean_ctor_get(v_results_2349_, 1);
v___x_2441_ = lean_unsigned_to_nat(0u);
v___x_2442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__0);
v___x_2443_ = lean_array_get_size(v_buckets_2440_);
v___x_2444_ = lean_nat_dec_lt(v___x_2441_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_dec(v_sp_2437_);
v___y_2406_ = v___y_2439_;
v___y_2407_ = v___y_2438_;
v_size_2408_ = v___x_2441_;
v_buckets_2409_ = v___x_2442_;
goto v___jp_2405_;
}
else
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___closed__1);
v___x_2446_ = lean_nat_dec_le(v___x_2443_, v___x_2443_);
if (v___x_2446_ == 0)
{
if (v___x_2444_ == 0)
{
lean_dec(v_sp_2437_);
v___y_2406_ = v___y_2439_;
v___y_2407_ = v___y_2438_;
v_size_2408_ = v___x_2441_;
v_buckets_2409_ = v___x_2442_;
goto v___jp_2405_;
}
else
{
size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = ((size_t)0ULL);
v___x_2448_ = lean_usize_of_nat(v___x_2443_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2350_, v_sp_2437_, v_buckets_2440_, v___x_2447_, v___x_2448_, v___x_2445_, v___y_2438_, v___y_2439_);
v___y_2422_ = v___y_2439_;
v___y_2423_ = v___y_2438_;
v___y_2424_ = v___x_2449_;
goto v___jp_2421_;
}
}
else
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = ((size_t)0ULL);
v___x_2451_ = lean_usize_of_nat(v___x_2443_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2350_, v_sp_2437_, v_buckets_2440_, v___x_2450_, v___x_2451_, v___x_2445_, v___y_2438_, v___y_2439_);
v___y_2422_ = v___y_2439_;
v___y_2423_ = v___y_2438_;
v___y_2424_ = v___x_2452_;
goto v___jp_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object* v_results_2469_, lean_object* v_useErrorFormat_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
uint8_t v_useErrorFormat_boxed_2474_; lean_object* v_res_2475_; 
v_useErrorFormat_boxed_2474_ = lean_unbox(v_useErrorFormat_2470_);
v_res_2475_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_results_2469_, v_useErrorFormat_boxed_2474_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec_ref(v_results_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object* v_n_2476_, lean_object* v_as_2477_, lean_object* v_lo_2478_, lean_object* v_hi_2479_, lean_object* v_w_2480_, lean_object* v_hlo_2481_, lean_object* v_hhi_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2476_, v_as_2477_, v_lo_2478_, v_hi_2479_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object* v_n_2484_, lean_object* v_as_2485_, lean_object* v_lo_2486_, lean_object* v_hi_2487_, lean_object* v_w_2488_, lean_object* v_hlo_2489_, lean_object* v_hhi_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(v_n_2484_, v_as_2485_, v_lo_2486_, v_hi_2487_, v_w_2488_, v_hlo_2489_, v_hhi_2490_);
lean_dec(v_hi_2487_);
lean_dec(v_n_2484_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object* v_00_u03b2_2492_, lean_object* v_m_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2493_, v_a_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object* v_00_u03b2_2496_, lean_object* v_m_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(v_00_u03b2_2496_, v_m_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_m_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object* v_n_2500_, lean_object* v_lo_2501_, lean_object* v_hi_2502_, lean_object* v_hhi_2503_, lean_object* v_pivot_2504_, lean_object* v_as_2505_, lean_object* v_i_2506_, lean_object* v_k_2507_, lean_object* v_ilo_2508_, lean_object* v_ik_2509_, lean_object* v_w_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2502_, v_pivot_2504_, v_as_2505_, v_i_2506_, v_k_2507_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object* v_n_2512_, lean_object* v_lo_2513_, lean_object* v_hi_2514_, lean_object* v_hhi_2515_, lean_object* v_pivot_2516_, lean_object* v_as_2517_, lean_object* v_i_2518_, lean_object* v_k_2519_, lean_object* v_ilo_2520_, lean_object* v_ik_2521_, lean_object* v_w_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(v_n_2512_, v_lo_2513_, v_hi_2514_, v_hhi_2515_, v_pivot_2516_, v_as_2517_, v_i_2518_, v_k_2519_, v_ilo_2520_, v_ik_2521_, v_w_2522_);
lean_dec(v_hi_2514_);
lean_dec(v_lo_2513_);
lean_dec(v_n_2512_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object* v_00_u03b2_2524_, lean_object* v_a_2525_, lean_object* v_x_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2525_, v_x_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2528_, lean_object* v_a_2529_, lean_object* v_x_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(v_00_u03b2_2528_, v_a_2529_, v_x_2530_);
lean_dec(v_x_2530_);
lean_dec(v_a_2529_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t v_sz_2532_, size_t v_i_2533_, lean_object* v_bs_2534_){
_start:
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_usize_dec_lt(v_i_2533_, v_sz_2532_);
if (v___x_2535_ == 0)
{
return v_bs_2534_;
}
else
{
lean_object* v_v_2536_; lean_object* v_snd_2537_; lean_object* v_size_2538_; lean_object* v___x_2539_; lean_object* v_bs_x27_2540_; size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v_v_2536_ = lean_array_uget_borrowed(v_bs_2534_, v_i_2533_);
v_snd_2537_ = lean_ctor_get(v_v_2536_, 1);
v_size_2538_ = lean_ctor_get(v_snd_2537_, 0);
lean_inc(v_size_2538_);
v___x_2539_ = lean_unsigned_to_nat(0u);
v_bs_x27_2540_ = lean_array_uset(v_bs_2534_, v_i_2533_, v___x_2539_);
v___x_2541_ = ((size_t)1ULL);
v___x_2542_ = lean_usize_add(v_i_2533_, v___x_2541_);
v___x_2543_ = lean_array_uset(v_bs_x27_2540_, v_i_2533_, v_size_2538_);
v_i_2533_ = v___x_2542_;
v_bs_2534_ = v___x_2543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object* v_sz_2545_, lean_object* v_i_2546_, lean_object* v_bs_2547_){
_start:
{
size_t v_sz_boxed_2548_; size_t v_i_boxed_2549_; lean_object* v_res_2550_; 
v_sz_boxed_2548_ = lean_unbox_usize(v_sz_2545_);
lean_dec(v_sz_2545_);
v_i_boxed_2549_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_boxed_2548_, v_i_boxed_2549_, v_bs_2547_);
return v_res_2550_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0));
v___x_2553_ = l_Lean_stringToMessageData(v___x_2552_);
return v___x_2553_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2));
v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
return v___x_2556_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4));
v___x_2559_ = l_Lean_stringToMessageData(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t v_useErrorFormat_2563_, uint8_t v_verbose_2564_, uint8_t v_groupByFilename_2565_, lean_object* v_as_2566_, size_t v_i_2567_, size_t v_stop_2568_, lean_object* v_b_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_a_2574_; lean_object* v_val_2579_; uint8_t v___x_2581_; 
v___x_2581_ = lean_usize_dec_eq(v_i_2567_, v_stop_2568_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v_fst_2583_; lean_object* v_snd_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2648_; 
v___x_2582_ = lean_array_uget(v_as_2566_, v_i_2567_);
v_fst_2583_ = lean_ctor_get(v___x_2582_, 0);
v_snd_2584_ = lean_ctor_get(v___x_2582_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2586_ = v___x_2582_;
v_isShared_2587_ = v_isSharedCheck_2648_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_snd_2584_);
lean_inc(v_fst_2583_);
lean_dec(v___x_2582_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2648_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v_warnings_2589_; lean_object* v_size_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; uint8_t v___x_2620_; 
v_size_2617_ = lean_ctor_get(v_snd_2584_, 0);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_nat_dec_eq(v_size_2617_, v___x_2618_);
v___x_2620_ = lean_bool_not(v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2586_);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_snd_2584_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; lean_object* v_unused_2636_; 
v_unused_2635_ = lean_ctor_get(v_snd_2584_, 1);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_snd_2584_, 0);
lean_dec(v_unused_2636_);
v___x_2622_ = v_snd_2584_;
v_isShared_2623_ = v_isSharedCheck_2634_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v_snd_2584_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2634_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
uint8_t v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = 2;
v___x_2625_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_verbose_2564_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_del_object(v___x_2622_);
lean_dec(v_fst_2583_);
v_a_2574_ = v_b_2569_;
goto v___jp_2573_;
}
else
{
lean_object* v_toEnvLinter_2626_; lean_object* v_noErrorsFound_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v_toEnvLinter_2626_ = lean_ctor_get(v_fst_2583_, 0);
lean_inc_ref(v_toEnvLinter_2626_);
lean_dec(v_fst_2583_);
v_noErrorsFound_2627_ = lean_ctor_get(v_toEnvLinter_2626_, 1);
lean_inc_ref(v_noErrorsFound_2627_);
lean_dec_ref(v_toEnvLinter_2626_);
v___x_2628_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 7);
lean_ctor_set(v___x_2622_, 1, v_noErrorsFound_2627_);
lean_ctor_set(v___x_2622_, 0, v___x_2628_);
v___x_2630_ = v___x_2622_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_noErrorsFound_2627_);
v___x_2630_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v_val_2579_ = v___x_2632_;
goto v___jp_2578_;
}
}
}
}
else
{
if (v_groupByFilename_2565_ == 0)
{
if (v_useErrorFormat_2563_ == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2638_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2584_, v___x_2637_, v_useErrorFormat_2563_, v___y_2570_, v___y_2571_);
lean_dec(v_snd_2584_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v_warnings_2589_ = v_a_2639_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_del_object(v___x_2586_);
lean_dec(v_fst_2583_);
lean_dec_ref(v_b_2569_);
v_a_2640_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2638_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2638_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
else
{
goto v___jp_2606_;
}
}
else
{
goto v___jp_2606_;
}
}
v___jp_2588_:
{
lean_object* v_toEnvLinter_2590_; lean_object* v_optName_2591_; lean_object* v_errorsFound_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v_toEnvLinter_2590_ = lean_ctor_get(v_fst_2583_, 0);
lean_inc_ref(v_toEnvLinter_2590_);
v_optName_2591_ = lean_ctor_get(v_fst_2583_, 1);
lean_inc(v_optName_2591_);
lean_dec(v_fst_2583_);
v_errorsFound_2592_ = lean_ctor_get(v_toEnvLinter_2590_, 2);
lean_inc_ref(v_errorsFound_2592_);
lean_dec_ref(v_toEnvLinter_2590_);
v___x_2593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1);
v___x_2594_ = l_Lean_MessageData_ofName(v_optName_2591_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set_tag(v___x_2586_, 7);
lean_ctor_set(v___x_2586_, 1, v___x_2594_);
lean_ctor_set(v___x_2586_, 0, v___x_2593_);
v___x_2596_ = v___x_2586_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v_errorsFound_2592_);
v___x_2600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v_warnings_2589_);
v___x_2603_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v_val_2579_ = v___x_2604_;
goto v___jp_2578_;
}
}
v___jp_2606_:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_snd_2584_, v_useErrorFormat_2563_, v___y_2570_, v___y_2571_);
lean_dec(v_snd_2584_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v_warnings_2589_ = v_a_2608_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_del_object(v___x_2586_);
lean_dec(v_fst_2583_);
lean_dec_ref(v_b_2569_);
v_a_2609_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2607_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
else
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_b_2569_);
return v___x_2649_;
}
v___jp_2573_:
{
size_t v___x_2575_; size_t v___x_2576_; 
v___x_2575_ = ((size_t)1ULL);
v___x_2576_ = lean_usize_add(v_i_2567_, v___x_2575_);
v_i_2567_ = v___x_2576_;
v_b_2569_ = v_a_2574_;
goto _start;
}
v___jp_2578_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_array_push(v_b_2569_, v_val_2579_);
v_a_2574_ = v___x_2580_;
goto v___jp_2573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object* v_useErrorFormat_2650_, lean_object* v_verbose_2651_, lean_object* v_groupByFilename_2652_, lean_object* v_as_2653_, lean_object* v_i_2654_, lean_object* v_stop_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_useErrorFormat_boxed_2660_; uint8_t v_verbose_boxed_2661_; uint8_t v_groupByFilename_boxed_2662_; size_t v_i_boxed_2663_; size_t v_stop_boxed_2664_; lean_object* v_res_2665_; 
v_useErrorFormat_boxed_2660_ = lean_unbox(v_useErrorFormat_2650_);
v_verbose_boxed_2661_ = lean_unbox(v_verbose_2651_);
v_groupByFilename_boxed_2662_ = lean_unbox(v_groupByFilename_2652_);
v_i_boxed_2663_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_stop_boxed_2664_ = lean_unbox_usize(v_stop_2655_);
lean_dec(v_stop_2655_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_boxed_2660_, v_verbose_boxed_2661_, v_groupByFilename_boxed_2662_, v_as_2653_, v_i_boxed_2663_, v_stop_boxed_2664_, v_b_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec_ref(v_as_2653_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t v_useErrorFormat_2668_, uint8_t v_verbose_2669_, uint8_t v_groupByFilename_2670_, lean_object* v_as_2671_, lean_object* v_start_2672_, lean_object* v_stop_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0));
v___x_2678_ = lean_nat_dec_lt(v_start_2672_, v_stop_2673_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___x_2680_ = lean_array_get_size(v_as_2671_);
v___x_2681_ = lean_nat_dec_le(v_stop_2673_, v___x_2680_);
if (v___x_2681_ == 0)
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_nat_dec_lt(v_start_2672_, v___x_2680_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2677_);
return v___x_2683_;
}
else
{
size_t v___x_2684_; size_t v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_usize_of_nat(v_start_2672_);
v___x_2685_ = lean_usize_of_nat(v___x_2680_);
v___x_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2668_, v_verbose_2669_, v_groupByFilename_2670_, v_as_2671_, v___x_2684_, v___x_2685_, v___x_2677_, v___y_2674_, v___y_2675_);
return v___x_2686_;
}
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_usize_of_nat(v_start_2672_);
v___x_2688_ = lean_usize_of_nat(v_stop_2673_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2668_, v_verbose_2669_, v_groupByFilename_2670_, v_as_2671_, v___x_2687_, v___x_2688_, v___x_2677_, v___y_2674_, v___y_2675_);
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object* v_useErrorFormat_2690_, lean_object* v_verbose_2691_, lean_object* v_groupByFilename_2692_, lean_object* v_as_2693_, lean_object* v_start_2694_, lean_object* v_stop_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v_useErrorFormat_boxed_2699_; uint8_t v_verbose_boxed_2700_; uint8_t v_groupByFilename_boxed_2701_; lean_object* v_res_2702_; 
v_useErrorFormat_boxed_2699_ = lean_unbox(v_useErrorFormat_2690_);
v_verbose_boxed_2700_ = lean_unbox(v_verbose_2691_);
v_groupByFilename_boxed_2701_ = lean_unbox(v_groupByFilename_2692_);
v_res_2702_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_boxed_2699_, v_verbose_boxed_2700_, v_groupByFilename_boxed_2701_, v_as_2693_, v_start_2694_, v_stop_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v_stop_2695_);
lean_dec(v_start_2694_);
lean_dec_ref(v_as_2693_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object* v_as_2703_, size_t v_i_2704_, size_t v_stop_2705_, lean_object* v_b_2706_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_usize_dec_eq(v_i_2704_, v_stop_2705_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; size_t v___x_2710_; size_t v___x_2711_; 
v___x_2708_ = lean_array_uget_borrowed(v_as_2703_, v_i_2704_);
v___x_2709_ = lean_nat_add(v_b_2706_, v___x_2708_);
lean_dec(v_b_2706_);
v___x_2710_ = ((size_t)1ULL);
v___x_2711_ = lean_usize_add(v_i_2704_, v___x_2710_);
v_i_2704_ = v___x_2711_;
v_b_2706_ = v___x_2709_;
goto _start;
}
else
{
return v_b_2706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object* v_as_2713_, lean_object* v_i_2714_, lean_object* v_stop_2715_, lean_object* v_b_2716_){
_start:
{
size_t v_i_boxed_2717_; size_t v_stop_boxed_2718_; lean_object* v_res_2719_; 
v_i_boxed_2717_ = lean_unbox_usize(v_i_2714_);
lean_dec(v_i_2714_);
v_stop_boxed_2718_ = lean_unbox_usize(v_stop_2715_);
lean_dec(v_stop_2715_);
v_res_2719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v_as_2713_, v_i_boxed_2717_, v_stop_boxed_2718_, v_b_2716_);
lean_dec_ref(v_as_2713_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object* v_as_2720_, size_t v_i_2721_, size_t v_stop_2722_, lean_object* v_b_2723_, lean_object* v___y_2724_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_usize_dec_eq(v_i_2721_, v_stop_2722_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_array_uget_borrowed(v_as_2720_, v_i_2721_);
lean_inc(v___x_2727_);
v___x_2728_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v___x_2727_, v___y_2724_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v_a_2731_; uint8_t v___x_2735_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2735_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
if (v___x_2735_ == 0)
{
v_a_2731_ = v_b_2723_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2736_; 
lean_inc(v___x_2727_);
v___x_2736_ = lean_array_push(v_b_2723_, v___x_2727_);
v_a_2731_ = v___x_2736_;
goto v___jp_2730_;
}
v___jp_2730_:
{
size_t v___x_2732_; size_t v___x_2733_; 
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2721_, v___x_2732_);
v_i_2721_ = v___x_2733_;
v_b_2723_ = v_a_2731_;
goto _start;
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v_b_2723_);
v_a_2737_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2728_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2728_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_b_2723_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object* v_as_2746_, lean_object* v_i_2747_, lean_object* v_stop_2748_, lean_object* v_b_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
size_t v_i_boxed_2752_; size_t v_stop_boxed_2753_; lean_object* v_res_2754_; 
v_i_boxed_2752_ = lean_unbox_usize(v_i_2747_);
lean_dec(v_i_2747_);
v_stop_boxed_2753_ = lean_unbox_usize(v_stop_2748_);
lean_dec(v_stop_2748_);
v_res_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2746_, v_i_boxed_2752_, v_stop_boxed_2753_, v_b_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v_as_2746_);
return v_res_2754_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__0));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__2));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__4));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__6));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__8));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__10));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__12));
v___x_2775_ = l_Lean_stringToMessageData(v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object* v_results_2777_, lean_object* v_decls_2778_, uint8_t v_groupByFilename_2779_, lean_object* v_whereDesc_2780_, uint8_t v_verbose_2781_, lean_object* v_numLinters_2782_, uint8_t v_useErrorFormat_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = lean_unsigned_to_nat(0u);
v___x_2788_ = lean_array_get_size(v_results_2777_);
v___x_2789_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_2783_, v_verbose_2781_, v_groupByFilename_2779_, v_results_2777_, v___x_2787_, v___x_2788_, v_a_2784_, v_a_2785_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2881_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2881_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2881_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v_a_2849_; lean_object* v___y_2862_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2794_ = lean_array_to_list(v_a_2790_);
v___x_2795_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2796_ = l_Lean_MessageData_joinSep(v___x_2794_, v___x_2795_);
v___x_2797_ = lean_array_get_size(v_decls_2778_);
v___x_2872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_2873_ = lean_nat_dec_lt(v___x_2787_, v___x_2797_);
if (v___x_2873_ == 0)
{
v_a_2849_ = v___x_2872_;
goto v___jp_2848_;
}
else
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_nat_dec_le(v___x_2797_, v___x_2797_);
if (v___x_2874_ == 0)
{
if (v___x_2873_ == 0)
{
v_a_2849_ = v___x_2872_;
goto v___jp_2848_;
}
else
{
size_t v___x_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = ((size_t)0ULL);
v___x_2876_ = lean_usize_of_nat(v___x_2797_);
v___x_2877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2778_, v___x_2875_, v___x_2876_, v___x_2872_, v_a_2785_);
v___y_2862_ = v___x_2877_;
goto v___jp_2861_;
}
}
else
{
size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = lean_usize_of_nat(v___x_2797_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2778_, v___x_2878_, v___x_2879_, v___x_2872_, v_a_2785_);
v___y_2862_ = v___x_2880_;
goto v___jp_2861_;
}
}
v___jp_2798_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
lean_inc_ref(v___y_2801_);
v___x_2802_ = l_Lean_stringToMessageData(v___y_2801_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___y_2799_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__1, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = lean_nat_sub(v___x_2797_, v___y_2800_);
v___x_2807_ = l_Nat_reprFast(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = l_Lean_MessageData_ofFormat(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2805_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__3, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Nat_reprFast(v___y_2800_);
v___x_2814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
v___x_2815_ = l_Lean_MessageData_ofFormat(v___x_2814_);
v___x_2816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2812_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__5, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5);
v___x_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = l_Lean_stringToMessageData(v_whereDesc_2780_);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__7, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Nat_reprFast(v_numLinters_2782_);
v___x_2824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
v___x_2825_ = l_Lean_MessageData_ofFormat(v___x_2824_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2822_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__9, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2796_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2829_);
v___x_2831_ = v___x_2792_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
v___jp_2833_:
{
if (v_verbose_2781_ == 0)
{
lean_object* v___x_2836_; 
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_del_object(v___x_2792_);
lean_dec(v_numLinters_2782_);
lean_dec_ref(v_whereDesc_2780_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2796_);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2837_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__11, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11);
lean_inc(v___y_2835_);
v___x_2838_ = l_Nat_reprFast(v___y_2835_);
v___x_2839_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
v___x_2840_ = l_Lean_MessageData_ofFormat(v___x_2839_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2837_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__13, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_unsigned_to_nat(1u);
v___x_2845_ = lean_nat_dec_eq(v___y_2835_, v___x_2844_);
lean_dec(v___y_2835_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; 
v___x_2846_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__14));
v___y_2799_ = v___x_2843_;
v___y_2800_ = v___y_2834_;
v___y_2801_ = v___x_2846_;
goto v___jp_2798_;
}
else
{
lean_object* v___x_2847_; 
v___x_2847_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___y_2799_ = v___x_2843_;
v___y_2800_ = v___y_2834_;
v___y_2801_ = v___x_2847_;
goto v___jp_2798_;
}
}
}
v___jp_2848_:
{
lean_object* v___x_2850_; size_t v_sz_2851_; size_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2850_ = lean_array_get_size(v_a_2849_);
lean_dec_ref(v_a_2849_);
v_sz_2851_ = lean_array_size(v_results_2777_);
v___x_2852_ = ((size_t)0ULL);
v___x_2853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_2851_, v___x_2852_, v_results_2777_);
v___x_2854_ = lean_array_get_size(v___x_2853_);
v___x_2855_ = lean_nat_dec_lt(v___x_2787_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_dec_ref(v___x_2853_);
v___y_2834_ = v___x_2850_;
v___y_2835_ = v___x_2787_;
goto v___jp_2833_;
}
else
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_nat_dec_le(v___x_2854_, v___x_2854_);
if (v___x_2856_ == 0)
{
if (v___x_2855_ == 0)
{
lean_dec_ref(v___x_2853_);
v___y_2834_ = v___x_2850_;
v___y_2835_ = v___x_2787_;
goto v___jp_2833_;
}
else
{
size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_usize_of_nat(v___x_2854_);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_2853_, v___x_2852_, v___x_2857_, v___x_2787_);
lean_dec_ref(v___x_2853_);
v___y_2834_ = v___x_2850_;
v___y_2835_ = v___x_2858_;
goto v___jp_2833_;
}
}
else
{
size_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_usize_of_nat(v___x_2854_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_2853_, v___x_2852_, v___x_2859_, v___x_2787_);
lean_dec_ref(v___x_2853_);
v___y_2834_ = v___x_2850_;
v___y_2835_ = v___x_2860_;
goto v___jp_2833_;
}
}
}
v___jp_2861_:
{
if (lean_obj_tag(v___y_2862_) == 0)
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___y_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___y_2862_, 1);
v_a_2849_ = v_a_2863_;
goto v___jp_2848_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v___x_2796_);
lean_del_object(v___x_2792_);
lean_dec(v_numLinters_2782_);
lean_dec_ref(v_whereDesc_2780_);
lean_dec_ref(v_results_2777_);
v_a_2864_ = lean_ctor_get(v___y_2862_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___y_2862_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___y_2862_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___y_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_numLinters_2782_);
lean_dec_ref(v_whereDesc_2780_);
lean_dec_ref(v_results_2777_);
v_a_2882_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2789_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2789_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object* v_results_2890_, lean_object* v_decls_2891_, lean_object* v_groupByFilename_2892_, lean_object* v_whereDesc_2893_, lean_object* v_verbose_2894_, lean_object* v_numLinters_2895_, lean_object* v_useErrorFormat_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
uint8_t v_groupByFilename_boxed_2900_; uint8_t v_verbose_boxed_2901_; uint8_t v_useErrorFormat_boxed_2902_; lean_object* v_res_2903_; 
v_groupByFilename_boxed_2900_ = lean_unbox(v_groupByFilename_2892_);
v_verbose_boxed_2901_ = lean_unbox(v_verbose_2894_);
v_useErrorFormat_boxed_2902_ = lean_unbox(v_useErrorFormat_2896_);
v_res_2903_ = l_Lean_Linter_EnvLinter_formatLinterResults(v_results_2890_, v_decls_2891_, v_groupByFilename_boxed_2900_, v_whereDesc_2893_, v_verbose_boxed_2901_, v_numLinters_2895_, v_useErrorFormat_boxed_2902_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_decls_2891_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object* v_as_2904_, size_t v_i_2905_, size_t v_stop_2906_, lean_object* v_b_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2904_, v_i_2905_, v_stop_2906_, v_b_2907_, v___y_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object* v_as_2912_, lean_object* v_i_2913_, lean_object* v_stop_2914_, lean_object* v_b_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
size_t v_i_boxed_2919_; size_t v_stop_boxed_2920_; lean_object* v_res_2921_; 
v_i_boxed_2919_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_stop_boxed_2920_ = lean_unbox_usize(v_stop_2914_);
lean_dec(v_stop_2914_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(v_as_2912_, v_i_boxed_2919_, v_stop_boxed_2920_, v_b_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v_as_2912_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object* v_r_2922_, lean_object* v_k_2923_, lean_object* v_x_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_array_push(v_r_2922_, v_k_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object* v_r_2926_, lean_object* v_k_2927_, lean_object* v_x_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(v_r_2926_, v_k_2927_, v_x_2928_);
lean_dec_ref(v_x_2928_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object* v_f_2930_, lean_object* v_x1_2931_, lean_object* v_x2_2932_, lean_object* v_x3_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_apply_3(v_f_2930_, v_x1_2931_, v_x2_2932_, v_x3_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2935_, lean_object* v_keys_2936_, lean_object* v_vals_2937_, lean_object* v_i_2938_, lean_object* v_acc_2939_){
_start:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_keys_2936_);
v___x_2941_ = lean_nat_dec_lt(v_i_2938_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_dec(v_i_2938_);
lean_dec(v_f_2935_);
return v_acc_2939_;
}
else
{
lean_object* v_k_2942_; lean_object* v_v_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_k_2942_ = lean_array_fget_borrowed(v_keys_2936_, v_i_2938_);
v_v_2943_ = lean_array_fget_borrowed(v_vals_2937_, v_i_2938_);
lean_inc(v_f_2935_);
lean_inc(v_v_2943_);
lean_inc(v_k_2942_);
v___x_2944_ = lean_apply_3(v_f_2935_, v_acc_2939_, v_k_2942_, v_v_2943_);
v___x_2945_ = lean_unsigned_to_nat(1u);
v___x_2946_ = lean_nat_add(v_i_2938_, v___x_2945_);
lean_dec(v_i_2938_);
v_i_2938_ = v___x_2946_;
v_acc_2939_ = v___x_2944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2948_, lean_object* v_keys_2949_, lean_object* v_vals_2950_, lean_object* v_i_2951_, lean_object* v_acc_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2948_, v_keys_2949_, v_vals_2950_, v_i_2951_, v_acc_2952_);
lean_dec_ref(v_vals_2950_);
lean_dec_ref(v_keys_2949_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_){
_start:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_object* v_es_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_es_2957_ = lean_ctor_get(v_x_2955_, 0);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_array_get_size(v_es_2957_);
v___x_2960_ = lean_nat_dec_lt(v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec(v_f_2954_);
return v_x_2956_;
}
else
{
uint8_t v___x_2961_; 
v___x_2961_ = lean_nat_dec_le(v___x_2959_, v___x_2959_);
if (v___x_2961_ == 0)
{
if (v___x_2960_ == 0)
{
lean_dec(v_f_2954_);
return v_x_2956_;
}
else
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((size_t)0ULL);
v___x_2963_ = lean_usize_of_nat(v___x_2959_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2954_, v_es_2957_, v___x_2962_, v___x_2963_, v_x_2956_);
return v___x_2964_;
}
}
else
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = lean_usize_of_nat(v___x_2959_);
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2954_, v_es_2957_, v___x_2965_, v___x_2966_, v_x_2956_);
return v___x_2967_;
}
}
}
else
{
lean_object* v_ks_2968_; lean_object* v_vs_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_ks_2968_ = lean_ctor_get(v_x_2955_, 0);
v_vs_2969_ = lean_ctor_get(v_x_2955_, 1);
v___x_2970_ = lean_unsigned_to_nat(0u);
v___x_2971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2954_, v_ks_2968_, v_vs_2969_, v___x_2970_, v_x_2956_);
return v___x_2971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2972_, lean_object* v_as_2973_, size_t v_i_2974_, size_t v_stop_2975_, lean_object* v_b_2976_){
_start:
{
lean_object* v___y_2978_; uint8_t v___x_2982_; 
v___x_2982_ = lean_usize_dec_eq(v_i_2974_, v_stop_2975_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_array_uget_borrowed(v_as_2973_, v_i_2974_);
switch(lean_obj_tag(v___x_2983_))
{
case 0:
{
lean_object* v_key_2984_; lean_object* v_val_2985_; lean_object* v___x_2986_; 
v_key_2984_ = lean_ctor_get(v___x_2983_, 0);
v_val_2985_ = lean_ctor_get(v___x_2983_, 1);
lean_inc(v_f_2972_);
lean_inc(v_val_2985_);
lean_inc(v_key_2984_);
v___x_2986_ = lean_apply_3(v_f_2972_, v_b_2976_, v_key_2984_, v_val_2985_);
v___y_2978_ = v___x_2986_;
goto v___jp_2977_;
}
case 1:
{
lean_object* v_node_2987_; lean_object* v___x_2988_; 
v_node_2987_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_f_2972_);
v___x_2988_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_2972_, v_node_2987_, v_b_2976_);
v___y_2978_ = v___x_2988_;
goto v___jp_2977_;
}
default: 
{
v___y_2978_ = v_b_2976_;
goto v___jp_2977_;
}
}
}
else
{
lean_dec(v_f_2972_);
return v_b_2976_;
}
v___jp_2977_:
{
size_t v___x_2979_; size_t v___x_2980_; 
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = lean_usize_add(v_i_2974_, v___x_2979_);
v_i_2974_ = v___x_2980_;
v_b_2976_ = v___y_2978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2989_, lean_object* v_as_2990_, lean_object* v_i_2991_, lean_object* v_stop_2992_, lean_object* v_b_2993_){
_start:
{
size_t v_i_boxed_2994_; size_t v_stop_boxed_2995_; lean_object* v_res_2996_; 
v_i_boxed_2994_ = lean_unbox_usize(v_i_2991_);
lean_dec(v_i_2991_);
v_stop_boxed_2995_ = lean_unbox_usize(v_stop_2992_);
lean_dec(v_stop_2992_);
v_res_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2989_, v_as_2990_, v_i_boxed_2994_, v_stop_boxed_2995_, v_b_2993_);
lean_dec_ref(v_as_2990_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_2997_, v_x_2998_, v_x_2999_);
lean_dec_ref(v_x_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object* v_map_3001_, lean_object* v_f_3002_, lean_object* v_init_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; 
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3004_, 0, v_f_3002_);
v___x_3005_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v___f_3004_, v_map_3001_, v_init_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object* v_map_3006_, lean_object* v_f_3007_, lean_object* v_init_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3006_, v_f_3007_, v_init_3008_);
lean_dec_ref(v_map_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object* v_a_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v_env_3014_; lean_object* v___x_3015_; lean_object* v_map_u2082_3016_; lean_object* v___f_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3013_ = lean_st_ref_get(v_a_3011_);
v_env_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_env_3014_);
lean_dec(v___x_3013_);
v___x_3015_ = l_Lean_Environment_constants(v_env_3014_);
v_map_u2082_3016_ = lean_ctor_get(v___x_3015_, 1);
lean_inc_ref(v_map_u2082_3016_);
lean_dec_ref(v___x_3015_);
v___f_3017_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0));
v___x_3018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__4_spec__7___closed__0));
v___x_3019_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_u2082_3016_, v___f_3017_, v___x_3018_);
lean_dec_ref(v_map_u2082_3016_);
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3021_);
lean_dec(v_a_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3025_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule(v_a_3028_, v_a_3029_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object* v_00_u03c3_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_map_3034_, lean_object* v_f_3035_, lean_object* v_init_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3034_, v_f_3035_, v_init_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object* v_00_u03c3_3038_, lean_object* v_00_u03b2_3039_, lean_object* v_map_3040_, lean_object* v_f_3041_, lean_object* v_init_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(v_00_u03c3_3038_, v_00_u03b2_3039_, v_map_3040_, v_f_3041_, v_init_3042_);
lean_dec_ref(v_map_3040_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object* v_map_3044_, lean_object* v_f_3045_, lean_object* v_init_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3045_, v_map_3044_, v_init_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object* v_map_3048_, lean_object* v_f_3049_, lean_object* v_init_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(v_map_3048_, v_f_3049_, v_init_3050_);
lean_dec_ref(v_map_3048_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object* v_00_u03c3_3052_, lean_object* v_00_u03b2_3053_, lean_object* v_map_3054_, lean_object* v_f_3055_, lean_object* v_init_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3055_, v_map_3054_, v_init_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3058_, lean_object* v_00_u03b2_3059_, lean_object* v_map_3060_, lean_object* v_f_3061_, lean_object* v_init_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(v_00_u03c3_3058_, v_00_u03b2_3059_, v_map_3060_, v_f_3061_, v_init_3062_);
lean_dec_ref(v_map_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3064_, lean_object* v_00_u03b1_3065_, lean_object* v_00_u03b2_3066_, lean_object* v_f_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3067_, v_x_3068_, v_x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3071_, lean_object* v_00_u03b1_3072_, lean_object* v_00_u03b2_3073_, lean_object* v_f_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(v_00_u03c3_3071_, v_00_u03b1_3072_, v_00_u03b2_3073_, v_f_3074_, v_x_3075_, v_x_3076_);
lean_dec_ref(v_x_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3078_, lean_object* v_00_u03b2_3079_, lean_object* v_00_u03c3_3080_, lean_object* v_f_3081_, lean_object* v_as_3082_, size_t v_i_3083_, size_t v_stop_3084_, lean_object* v_b_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3081_, v_as_3082_, v_i_3083_, v_stop_3084_, v_b_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3087_, lean_object* v_00_u03b2_3088_, lean_object* v_00_u03c3_3089_, lean_object* v_f_3090_, lean_object* v_as_3091_, lean_object* v_i_3092_, lean_object* v_stop_3093_, lean_object* v_b_3094_){
_start:
{
size_t v_i_boxed_3095_; size_t v_stop_boxed_3096_; lean_object* v_res_3097_; 
v_i_boxed_3095_ = lean_unbox_usize(v_i_3092_);
lean_dec(v_i_3092_);
v_stop_boxed_3096_ = lean_unbox_usize(v_stop_3093_);
lean_dec(v_stop_3093_);
v_res_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3087_, v_00_u03b2_3088_, v_00_u03c3_3089_, v_f_3090_, v_as_3091_, v_i_boxed_3095_, v_stop_boxed_3096_, v_b_3094_);
lean_dec_ref(v_as_3091_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3098_, lean_object* v_00_u03b1_3099_, lean_object* v_00_u03b2_3100_, lean_object* v_f_3101_, lean_object* v_keys_3102_, lean_object* v_vals_3103_, lean_object* v_heq_3104_, lean_object* v_i_3105_, lean_object* v_acc_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3101_, v_keys_3102_, v_vals_3103_, v_i_3105_, v_acc_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3108_, lean_object* v_00_u03b1_3109_, lean_object* v_00_u03b2_3110_, lean_object* v_f_3111_, lean_object* v_keys_3112_, lean_object* v_vals_3113_, lean_object* v_heq_3114_, lean_object* v_i_3115_, lean_object* v_acc_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3108_, v_00_u03b1_3109_, v_00_u03b2_3110_, v_f_3111_, v_keys_3112_, v_vals_3113_, v_heq_3114_, v_i_3115_, v_acc_3116_);
lean_dec_ref(v_vals_3113_);
lean_dec_ref(v_keys_3112_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object* v_x_3118_, lean_object* v_x_3119_){
_start:
{
if (lean_obj_tag(v_x_3119_) == 0)
{
return v_x_3118_;
}
else
{
lean_object* v_key_3120_; lean_object* v_tail_3121_; lean_object* v___x_3122_; 
v_key_3120_ = lean_ctor_get(v_x_3119_, 0);
lean_inc(v_key_3120_);
v_tail_3121_ = lean_ctor_get(v_x_3119_, 2);
lean_inc(v_tail_3121_);
lean_dec_ref_known(v_x_3119_, 3);
v___x_3122_ = lean_array_push(v_x_3118_, v_key_3120_);
v_x_3118_ = v___x_3122_;
v_x_3119_ = v_tail_3121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object* v_as_3124_, size_t v_i_3125_, size_t v_stop_3126_, lean_object* v_b_3127_){
_start:
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_usize_dec_eq(v_i_3125_, v_stop_3126_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; size_t v___x_3131_; size_t v___x_3132_; 
v___x_3129_ = lean_array_uget_borrowed(v_as_3124_, v_i_3125_);
lean_inc(v___x_3129_);
v___x_3130_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(v_b_3127_, v___x_3129_);
v___x_3131_ = ((size_t)1ULL);
v___x_3132_ = lean_usize_add(v_i_3125_, v___x_3131_);
v_i_3125_ = v___x_3132_;
v_b_3127_ = v___x_3130_;
goto _start;
}
else
{
return v_b_3127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object* v_as_3134_, lean_object* v_i_3135_, lean_object* v_stop_3136_, lean_object* v_b_3137_){
_start:
{
size_t v_i_boxed_3138_; size_t v_stop_boxed_3139_; lean_object* v_res_3140_; 
v_i_boxed_3138_ = lean_unbox_usize(v_i_3135_);
lean_dec(v_i_3135_);
v_stop_boxed_3139_ = lean_unbox_usize(v_stop_3136_);
lean_dec(v_stop_3136_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_as_3134_, v_i_boxed_3138_, v_stop_boxed_3139_, v_b_3137_);
lean_dec_ref(v_as_3134_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v_a_3145_; lean_object* v_env_3146_; lean_object* v___x_3147_; lean_object* v_map_u2081_3148_; lean_object* v_buckets_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3143_ = lean_st_ref_get(v_a_3141_);
v___x_3144_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3141_);
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
v_env_3146_ = lean_ctor_get(v___x_3143_, 0);
lean_inc_ref(v_env_3146_);
lean_dec(v___x_3143_);
v___x_3147_ = l_Lean_Environment_constants(v_env_3146_);
v_map_u2081_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc_ref(v_map_u2081_3148_);
lean_dec_ref(v___x_3147_);
v_buckets_3149_ = lean_ctor_get(v_map_u2081_3148_, 1);
lean_inc_ref(v_buckets_3149_);
lean_dec_ref(v_map_u2081_3148_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = lean_array_get_size(v_buckets_3149_);
v___x_3152_ = lean_nat_dec_lt(v___x_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_dec_ref(v_buckets_3149_);
lean_dec(v_a_3145_);
return v___x_3144_;
}
else
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_le(v___x_3151_, v___x_3151_);
if (v___x_3153_ == 0)
{
if (v___x_3152_ == 0)
{
lean_dec_ref(v_buckets_3149_);
lean_dec(v_a_3145_);
return v___x_3144_;
}
else
{
lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3163_; 
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v___x_3144_, 0);
lean_dec(v_unused_3164_);
v___x_3155_ = v___x_3144_;
v_isShared_3156_ = v_isSharedCheck_3163_;
goto v_resetjp_3154_;
}
else
{
lean_dec(v___x_3144_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3163_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3151_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3149_, v___x_3157_, v___x_3158_, v_a_3145_);
lean_dec_ref(v_buckets_3149_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3159_);
v___x_3161_ = v___x_3155_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3174_; 
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_3144_, 0);
lean_dec(v_unused_3175_);
v___x_3166_ = v___x_3144_;
v_isShared_3167_ = v_isSharedCheck_3174_;
goto v_resetjp_3165_;
}
else
{
lean_dec(v___x_3144_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3174_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = lean_usize_of_nat(v___x_3151_);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3149_, v___x_3168_, v___x_3169_, v_a_3145_);
lean_dec_ref(v_buckets_3149_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3170_);
v___x_3172_ = v___x_3166_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3176_);
lean_dec(v_a_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_Linter_EnvLinter_getAllDecls(v_a_3183_, v_a_3184_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object* v_msg_3187_){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_unsigned_to_nat(0u);
v___x_3189_ = lean_panic_fn_borrowed(v___x_3188_, v_msg_3187_);
return v___x_3189_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3193_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2));
v___x_3194_ = lean_unsigned_to_nat(14u);
v___x_3195_ = lean_unsigned_to_nat(22u);
v___x_3196_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1));
v___x_3197_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0));
v___x_3198_ = l_mkPanicMessageWithDecl(v___x_3197_, v___x_3196_, v___x_3195_, v___x_3194_, v___x_3193_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 0)
{
lean_dec_ref(v___x_3200_);
return v_x_3201_;
}
else
{
lean_object* v_key_3203_; lean_object* v_tail_3204_; uint8_t v___x_3205_; lean_object* v___y_3207_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v_key_3203_ = lean_ctor_get(v_x_3202_, 0);
lean_inc(v_key_3203_);
v_tail_3204_ = lean_ctor_get(v_x_3202_, 2);
lean_inc(v_tail_3204_);
lean_dec_ref_known(v_x_3202_, 3);
v___x_3205_ = 0;
lean_inc_ref(v___x_3200_);
v___x_3214_ = l_Lean_Environment_const2ModIdx(v___x_3200_);
v___x_3215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v___x_3214_, v_key_3203_);
lean_dec_ref(v___x_3214_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3);
v___x_3217_ = l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(v___x_3216_);
v___y_3207_ = v___x_3217_;
goto v___jp_3206_;
}
else
{
lean_object* v_val_3218_; 
v_val_3218_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v___x_3215_, 1);
v___y_3207_ = v_val_3218_;
goto v___jp_3206_;
}
v___jp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3208_ = lean_box(v___x_3205_);
v___x_3209_ = lean_array_get(v___x_3208_, v___x_3199_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec(v___x_3208_);
v___x_3210_ = lean_unbox(v___x_3209_);
lean_dec(v___x_3209_);
if (v___x_3210_ == 0)
{
lean_dec(v_key_3203_);
v_x_3202_ = v_tail_3204_;
goto _start;
}
else
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_array_push(v_x_3201_, v_key_3203_);
v_x_3201_ = v___x_3212_;
v_x_3202_ = v_tail_3204_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3219_, v___x_3220_, v_x_3221_, v_x_3222_);
lean_dec_ref(v___x_3219_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object* v___x_3224_, lean_object* v___x_3225_, lean_object* v_as_3226_, size_t v_i_3227_, size_t v_stop_3228_, lean_object* v_b_3229_){
_start:
{
uint8_t v___x_3230_; 
v___x_3230_ = lean_usize_dec_eq(v_i_3227_, v_stop_3228_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; size_t v___x_3233_; size_t v___x_3234_; 
v___x_3231_ = lean_array_uget_borrowed(v_as_3226_, v_i_3227_);
lean_inc(v___x_3231_);
lean_inc_ref(v___x_3225_);
v___x_3232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3224_, v___x_3225_, v_b_3229_, v___x_3231_);
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_add(v_i_3227_, v___x_3233_);
v_i_3227_ = v___x_3234_;
v_b_3229_ = v___x_3232_;
goto _start;
}
else
{
lean_dec_ref(v___x_3225_);
return v_b_3229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v_as_3238_, lean_object* v_i_3239_, lean_object* v_stop_3240_, lean_object* v_b_3241_){
_start:
{
size_t v_i_boxed_3242_; size_t v_stop_boxed_3243_; lean_object* v_res_3244_; 
v_i_boxed_3242_ = lean_unbox_usize(v_i_3239_);
lean_dec(v_i_3239_);
v_stop_boxed_3243_ = lean_unbox_usize(v_stop_3240_);
lean_dec(v_stop_3240_);
v_res_3244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3236_, v___x_3237_, v_as_3238_, v_i_boxed_3242_, v_stop_boxed_3243_, v_b_3241_);
lean_dec_ref(v_as_3238_);
lean_dec_ref(v___x_3236_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object* v_pkg_3245_, size_t v_sz_3246_, size_t v_i_3247_, lean_object* v_bs_3248_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_usize_dec_lt(v_i_3247_, v_sz_3246_);
if (v___x_3249_ == 0)
{
return v_bs_3248_;
}
else
{
lean_object* v_v_3250_; lean_object* v___x_3251_; lean_object* v_bs_x27_3252_; uint8_t v___x_3253_; size_t v___x_3254_; size_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_v_3250_ = lean_array_uget(v_bs_3248_, v_i_3247_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v_bs_x27_3252_ = lean_array_uset(v_bs_3248_, v_i_3247_, v___x_3251_);
v___x_3253_ = l_Lean_Name_isPrefixOf(v_pkg_3245_, v_v_3250_);
lean_dec(v_v_3250_);
v___x_3254_ = ((size_t)1ULL);
v___x_3255_ = lean_usize_add(v_i_3247_, v___x_3254_);
v___x_3256_ = lean_box(v___x_3253_);
v___x_3257_ = lean_array_uset(v_bs_x27_3252_, v_i_3247_, v___x_3256_);
v_i_3247_ = v___x_3255_;
v_bs_3248_ = v___x_3257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object* v_pkg_3259_, lean_object* v_sz_3260_, lean_object* v_i_3261_, lean_object* v_bs_3262_){
_start:
{
size_t v_sz_boxed_3263_; size_t v_i_boxed_3264_; lean_object* v_res_3265_; 
v_sz_boxed_3263_ = lean_unbox_usize(v_sz_3260_);
lean_dec(v_sz_3260_);
v_i_boxed_3264_ = lean_unbox_usize(v_i_3261_);
lean_dec(v_i_3261_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3259_, v_sz_boxed_3263_, v_i_boxed_3264_, v_bs_3262_);
lean_dec(v_pkg_3259_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object* v_pkg_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v_a_3271_; lean_object* v_env_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_map_u2081_3275_; lean_object* v_buckets_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3269_ = lean_st_ref_get(v_a_3267_);
v___x_3270_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3267_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
v_env_3272_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref_n(v_env_3272_, 2);
lean_dec(v___x_3269_);
v___x_3273_ = l_Lean_Environment_header(v_env_3272_);
v___x_3274_ = l_Lean_Environment_constants(v_env_3272_);
v_map_u2081_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc_ref(v_map_u2081_3275_);
lean_dec_ref(v___x_3274_);
v_buckets_3276_ = lean_ctor_get(v_map_u2081_3275_, 1);
lean_inc_ref(v_buckets_3276_);
lean_dec_ref(v_map_u2081_3275_);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = lean_array_get_size(v_buckets_3276_);
v___x_3279_ = lean_nat_dec_lt(v___x_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_dec_ref(v_buckets_3276_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v_env_3272_);
lean_dec(v_a_3271_);
return v___x_3270_;
}
else
{
lean_object* v___x_3280_; size_t v_sz_3281_; size_t v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3280_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3273_);
v_sz_3281_ = lean_array_size(v___x_3280_);
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3266_, v_sz_3281_, v___x_3282_, v___x_3280_);
v___x_3284_ = lean_nat_dec_le(v___x_3278_, v___x_3278_);
if (v___x_3284_ == 0)
{
if (v___x_3279_ == 0)
{
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_buckets_3276_);
lean_dec_ref(v_env_3272_);
lean_dec(v_a_3271_);
return v___x_3270_;
}
else
{
lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3293_; 
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v___x_3270_, 0);
lean_dec(v_unused_3294_);
v___x_3286_ = v___x_3270_;
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
else
{
lean_dec(v___x_3270_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
size_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3288_ = lean_usize_of_nat(v___x_3278_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3283_, v_env_3272_, v_buckets_3276_, v___x_3282_, v___x_3288_, v_a_3271_);
lean_dec_ref(v_buckets_3276_);
lean_dec_ref(v___x_3283_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3289_);
v___x_3291_ = v___x_3286_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3303_; 
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; 
v_unused_3304_ = lean_ctor_get(v___x_3270_, 0);
lean_dec(v_unused_3304_);
v___x_3296_ = v___x_3270_;
v_isShared_3297_ = v_isSharedCheck_3303_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3270_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3303_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
size_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3298_ = lean_usize_of_nat(v___x_3278_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3283_, v_env_3272_, v_buckets_3276_, v___x_3282_, v___x_3298_, v_a_3271_);
lean_dec_ref(v_buckets_3276_);
lean_dec_ref(v___x_3283_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v___x_3299_);
v___x_3301_ = v___x_3296_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object* v_pkg_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec(v_pkg_3305_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object* v_pkg_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3309_, v_a_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object* v_pkg_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Linter_EnvLinter_getDeclsInPackage(v_pkg_3314_, v_a_3315_, v_a_3316_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_pkg_3314_);
return v_res_3318_;
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

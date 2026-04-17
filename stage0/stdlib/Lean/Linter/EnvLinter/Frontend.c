// Lean compiler output
// Module: Lean.Linter.EnvLinter.Frontend
// Imports: public import Lean.Linter.EnvLinter.Basic import Lean.DeclarationRange import Lean.Util.Path import Lean.CoreM import Lean.Elab.Command
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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_Linter_EnvLinter_builtinNolintAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_EnvLinter_envLinterExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_EnvLinter_getChecks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_EnvLinter_getChecks___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_getChecks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "-- (non-clippy linters skipped)\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__1;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " declarations (plus "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__5;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " automatically generated ones) "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__7;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__9;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " linters\n\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__11;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-- Found "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__12 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__13;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " error"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__14 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__15;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__16 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(lean_object* v_x1_145_, lean_object* v_x2_146_){
_start:
{
lean_object* v_name_147_; lean_object* v_name_148_; uint8_t v___x_149_; 
v_name_147_ = lean_ctor_get(v_x1_145_, 1);
v_name_148_ = lean_ctor_get(v_x2_146_, 1);
v___x_149_ = l_Lean_Name_lt(v_name_147_, v_name_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0___boxed(lean_object* v_x1_150_, lean_object* v_x2_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_x1_150_, v_x2_151_);
lean_dec_ref(v_x2_151_);
lean_dec_ref(v_x1_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(lean_object* v_a_154_, lean_object* v_as_155_, lean_object* v_k_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_mid_161_; lean_object* v_midVal_162_; uint8_t v___x_163_; 
v___x_159_ = lean_nat_add(v_x_157_, v_x_158_);
v___x_160_ = lean_unsigned_to_nat(1u);
v_mid_161_ = lean_nat_shiftr(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
v_midVal_162_ = lean_array_fget_borrowed(v_as_155_, v_mid_161_);
v___x_163_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_midVal_162_, v_k_156_);
if (v___x_163_ == 0)
{
uint8_t v___x_164_; 
lean_dec(v_x_158_);
v___x_164_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_156_, v_midVal_162_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg___boxed(lean_object* v_a_177_, lean_object* v_as_178_, lean_object* v_k_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_177_, v_as_178_, v_k_179_, v_x_180_, v_x_181_);
lean_dec_ref(v_k_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(lean_object* v_a_183_, lean_object* v_as_184_, lean_object* v_k_185_){
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
v___x_190_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_185_, v___x_189_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; 
v___x_191_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v___x_189_, v_k_185_);
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
v___x_199_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v___x_198_, v_k_185_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_185_, v___x_198_);
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
v___x_205_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_183_, v_as_184_, v_k_185_, v___x_187_, v___x_197_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___boxed(lean_object* v_a_210_, lean_object* v_as_211_, lean_object* v_k_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(v_a_210_, v_as_211_, v_k_212_);
lean_dec_ref(v_k_212_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
uint8_t v___x_216_; 
v___x_216_ = 0;
return v___x_216_;
}
else
{
lean_object* v_head_217_; lean_object* v_tail_218_; uint8_t v___x_219_; 
v_head_217_ = lean_ctor_get(v_x_215_, 0);
v_tail_218_ = lean_ctor_get(v_x_215_, 1);
v___x_219_ = lean_name_eq(v_a_214_, v_head_217_);
if (v___x_219_ == 0)
{
v_x_215_ = v_tail_218_;
goto _start;
}
else
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1___boxed(lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_a_221_, v_x_222_);
lean_dec(v_x_222_);
lean_dec(v_a_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(lean_object* v_runOnly_225_, uint8_t v_clippy_226_, lean_object* v_init_227_, lean_object* v_x_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_d_233_; 
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_l_238_; lean_object* v_r_239_; lean_object* v___x_240_; 
v_k_236_ = lean_ctor_get(v_x_228_, 1);
lean_inc(v_k_236_);
v_v_237_ = lean_ctor_get(v_x_228_, 2);
lean_inc(v_v_237_);
v_l_238_ = lean_ctor_get(v_x_228_, 3);
lean_inc(v_l_238_);
v_r_239_ = lean_ctor_get(v_x_228_, 4);
lean_inc(v_r_239_);
lean_dec_ref(v_x_228_);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_225_, v_clippy_226_, v_init_227_, v_l_238_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v_a_242_; 
lean_dec_ref(v___x_240_);
lean_dec(v_r_239_);
lean_dec(v_v_237_);
lean_dec(v_k_236_);
v_a_242_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref(v_a_241_);
v_d_233_ = v_a_242_;
goto v___jp_232_;
}
else
{
lean_object* v_a_243_; lean_object* v_fst_244_; lean_object* v_snd_245_; uint8_t v___y_260_; 
v_a_243_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_a_243_);
lean_dec_ref(v_a_241_);
v_fst_244_ = lean_ctor_get(v_v_237_, 0);
lean_inc(v_fst_244_);
v_snd_245_ = lean_ctor_get(v_v_237_, 1);
lean_inc(v_snd_245_);
lean_dec(v_v_237_);
if (lean_obj_tag(v_runOnly_225_) == 0)
{
if (v_clippy_226_ == 0)
{
uint8_t v___x_265_; 
v___x_265_ = lean_unbox(v_snd_245_);
lean_dec(v_snd_245_);
v___y_260_ = v___x_265_;
goto v___jp_259_;
}
else
{
lean_dec(v_snd_245_);
lean_dec_ref(v___x_240_);
goto v___jp_246_;
}
}
else
{
lean_object* v_val_266_; uint8_t v___x_267_; 
lean_dec(v_snd_245_);
v_val_266_ = lean_ctor_get(v_runOnly_225_, 0);
v___x_267_ = l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_k_236_, v_val_266_);
v___y_260_ = v___x_267_;
goto v___jp_259_;
}
v___jp_246_:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_k_236_, v_fst_244_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc_n(v_a_248_, 2);
lean_dec_ref(v___x_247_);
v___x_249_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(v_a_248_, v_a_243_, v_a_248_);
lean_dec(v_a_248_);
v_init_227_ = v___x_249_;
v_x_228_ = v_r_239_;
goto _start;
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_a_243_);
lean_dec(v_r_239_);
v_a_251_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_247_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_247_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
v___jp_259_:
{
if (v___y_260_ == 0)
{
lean_dec(v_fst_244_);
lean_dec(v_a_243_);
lean_dec(v_k_236_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_261_; 
v_a_261_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_240_);
if (lean_obj_tag(v_a_261_) == 0)
{
lean_object* v_a_262_; 
lean_dec(v_r_239_);
v_a_262_ = lean_ctor_get(v_a_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v_a_261_);
v_d_233_ = v_a_262_;
goto v___jp_232_;
}
else
{
lean_object* v_a_263_; 
v_a_263_ = lean_ctor_get(v_a_261_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v_a_261_);
v_init_227_ = v_a_263_;
v_x_228_ = v_r_239_;
goto _start;
}
}
else
{
lean_dec(v_r_239_);
return v___x_240_;
}
}
else
{
lean_dec_ref(v___x_240_);
goto v___jp_246_;
}
}
}
}
else
{
lean_dec(v_r_239_);
lean_dec(v_v_237_);
lean_dec(v_k_236_);
return v___x_240_;
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_init_227_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_d_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2___boxed(lean_object* v_runOnly_270_, lean_object* v_clippy_271_, lean_object* v_init_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
uint8_t v_clippy_boxed_277_; lean_object* v_res_278_; 
v_clippy_boxed_277_ = lean_unbox(v_clippy_271_);
v_res_278_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_270_, v_clippy_boxed_277_, v_init_272_, v_x_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v_runOnly_270_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t v_clippy_281_, lean_object* v_runOnly_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; lean_object* v_env_287_; lean_object* v___x_288_; lean_object* v_toEnvExtension_289_; lean_object* v_asyncMode_290_; lean_object* v___x_291_; lean_object* v_result_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_286_ = lean_st_ref_get(v_a_284_);
v_env_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_ref(v_env_287_);
lean_dec(v___x_286_);
v___x_288_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_289_ = lean_ctor_get(v___x_288_, 0);
v_asyncMode_290_ = lean_ctor_get(v_toEnvExtension_289_, 2);
v___x_291_ = lean_box(1);
v_result_292_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getChecks___closed__0));
v___x_293_ = lean_box(0);
v___x_294_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_291_, v___x_288_, v_env_287_, v_asyncMode_290_, v___x_293_);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_282_, v_clippy_281_, v_result_292_, v___x_294_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_a_300_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v_a_296_, 0);
lean_inc(v_a_300_);
lean_dec(v_a_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_a_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_a_305_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_295_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_295_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks___boxed(lean_object* v_clippy_313_, lean_object* v_runOnly_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
uint8_t v_clippy_boxed_318_; lean_object* v_res_319_; 
v_clippy_boxed_318_ = lean_unbox(v_clippy_313_);
v_res_319_ = l_Lean_Linter_EnvLinter_getChecks(v_clippy_boxed_318_, v_runOnly_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_runOnly_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(lean_object* v_a_320_, lean_object* v_as_321_, lean_object* v_k_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_320_, v_as_321_, v_k_322_, v_x_323_, v_x_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___boxed(lean_object* v_a_328_, lean_object* v_as_329_, lean_object* v_k_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(v_a_328_, v_as_329_, v_k_330_, v_x_331_, v_x_332_, v_x_333_, v_x_334_);
lean_dec_ref(v_k_330_);
return v_res_335_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(lean_object* v_a_336_, lean_object* v_as_337_, size_t v_i_338_, size_t v_stop_339_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_eq(v_i_338_, v_stop_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_array_uget_borrowed(v_as_337_, v_i_338_);
v___x_342_ = lean_name_eq(v_a_336_, v___x_341_);
if (v___x_342_ == 0)
{
size_t v___x_343_; size_t v___x_344_; 
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_338_, v___x_343_);
v_i_338_ = v___x_344_;
goto _start;
}
else
{
return v___x_342_;
}
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8___boxed(lean_object* v_a_347_, lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_stop_350_){
_start:
{
size_t v_i_boxed_351_; size_t v_stop_boxed_352_; uint8_t v_res_353_; lean_object* v_r_354_; 
v_i_boxed_351_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_352_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_347_, v_as_348_, v_i_boxed_351_, v_stop_boxed_352_);
lean_dec_ref(v_as_348_);
lean_dec(v_a_347_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(lean_object* v_as_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_array_get_size(v_as_355_);
v___x_359_ = lean_nat_dec_lt(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
return v___x_359_;
}
else
{
if (v___x_359_ == 0)
{
return v___x_359_;
}
else
{
size_t v___x_360_; size_t v___x_361_; uint8_t v___x_362_; 
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_358_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_356_, v_as_355_, v___x_360_, v___x_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6___boxed(lean_object* v_as_363_, lean_object* v_a_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v_as_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_as_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Array_instInhabited(lean_box(0));
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(lean_object* v_linter_370_, lean_object* v_decl_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___y_376_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_374_ = lean_st_ref_get(v___y_372_);
v_env_384_ = lean_ctor_get(v___x_374_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_374_);
v___x_385_ = lean_obj_once(&l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0, &l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once, _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0);
v___x_386_ = l_Lean_Linter_EnvLinter_builtinNolintAttr;
v___x_387_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_385_, v___x_386_, v_env_384_, v_decl_371_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___y_376_ = v___x_388_;
goto v___jp_375_;
}
else
{
lean_object* v_val_389_; 
v_val_389_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_389_);
lean_dec_ref(v___x_387_);
v___y_376_ = v_val_389_;
goto v___jp_375_;
}
v___jp_375_:
{
uint8_t v___x_377_; 
v___x_377_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v___y_376_, v_linter_370_);
lean_dec_ref(v___y_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = 1;
v___x_379_ = lean_box(v___x_378_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
else
{
uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = 0;
v___x_382_ = lean_box(v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___boxed(lean_object* v_linter_390_, lean_object* v_decl_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_390_, v_decl_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec(v_linter_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object* v___x_395_, lean_object* v_as_396_, size_t v_i_397_, size_t v_stop_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_eq(v_i_397_, v_stop_398_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_array_uget_borrowed(v_as_396_, v_i_397_);
lean_inc(v___x_404_);
v___x_405_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v___x_395_, v___x_404_, v___y_401_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v_a_408_; uint8_t v___x_412_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___x_412_ = lean_unbox(v_a_406_);
lean_dec(v_a_406_);
if (v___x_412_ == 0)
{
v_a_408_ = v_b_399_;
goto v___jp_407_;
}
else
{
lean_object* v___x_413_; 
lean_inc(v___x_404_);
v___x_413_ = lean_array_push(v_b_399_, v___x_404_);
v_a_408_ = v___x_413_;
goto v___jp_407_;
}
v___jp_407_:
{
size_t v___x_409_; size_t v___x_410_; 
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_add(v_i_397_, v___x_409_);
v_i_397_ = v___x_410_;
v_b_399_ = v_a_408_;
goto _start;
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_b_399_);
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
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_b_399_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object* v___x_423_, lean_object* v_as_424_, lean_object* v_i_425_, lean_object* v_stop_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
size_t v_i_boxed_431_; size_t v_stop_boxed_432_; lean_object* v_res_433_; 
v_i_boxed_431_ = lean_unbox_usize(v_i_425_);
lean_dec(v_i_425_);
v_stop_boxed_432_ = lean_unbox_usize(v_stop_426_);
lean_dec(v_stop_426_);
v_res_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v___x_423_, v_as_424_, v_i_boxed_431_, v_stop_boxed_432_, v_b_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v_as_424_);
lean_dec(v___x_423_);
return v_res_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_434_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_438_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
lean_ctor_set(v___x_438_, 2, v___x_437_);
lean_ctor_set(v___x_438_, 3, v___x_437_);
lean_ctor_set(v___x_438_, 4, v___x_437_);
lean_ctor_set(v___x_438_, 5, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(32u);
v___x_440_ = lean_mk_empty_array_with_capacity(v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_ctor_set(v___x_443_, 3, v___x_442_);
lean_ctor_set(v___x_443_, 4, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v_test_446_, lean_object* v_v_447_, lean_object* v_x_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; size_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_452_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
lean_inc_n(v___x_444_, 5);
v___x_453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_453_, 0, v___x_444_);
lean_ctor_set(v___x_453_, 1, v___x_444_);
lean_ctor_set(v___x_453_, 2, v___x_444_);
lean_ctor_set(v___x_453_, 3, v___x_444_);
lean_ctor_set(v___x_453_, 4, v___x_452_);
lean_ctor_set(v___x_453_, 5, v___x_452_);
lean_ctor_set(v___x_453_, 6, v___x_452_);
lean_ctor_set(v___x_453_, 7, v___x_452_);
lean_ctor_set(v___x_453_, 8, v___x_452_);
lean_ctor_set(v___x_453_, 9, v___x_452_);
v___x_454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2);
v___x_455_ = lean_unsigned_to_nat(32u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3);
v___x_458_ = ((size_t)5ULL);
v___x_459_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_456_);
lean_ctor_set(v___x_459_, 2, v___x_444_);
lean_ctor_set(v___x_459_, 3, v___x_444_);
lean_ctor_set_usize(v___x_459_, 4, v___x_458_);
v___x_460_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4);
v___x_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_461_, 0, v___x_453_);
lean_ctor_set(v___x_461_, 1, v___x_454_);
lean_ctor_set(v___x_461_, 2, v___x_445_);
lean_ctor_set(v___x_461_, 3, v___x_459_);
lean_ctor_set(v___x_461_, 4, v___x_460_);
v___x_462_ = lean_st_mk_ref(v___x_461_);
v___x_463_ = l_Lean_Elab_Command_mkMetaContext;
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___x_462_);
v___x_464_ = lean_apply_6(v_test_446_, v_v_447_, v___x_463_, v___x_462_, v___y_449_, v___y_450_, lean_box(0));
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_473_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_473_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_473_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_473_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_st_ref_get(v___x_462_);
lean_dec(v___x_462_);
lean_dec(v___x_469_);
if (v_isShared_468_ == 0)
{
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_465_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
else
{
lean_dec(v___x_462_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v_test_476_, lean_object* v_v_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(v___x_474_, v___x_475_, v_test_476_, v_v_477_, v_x_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object* v_a_483_, lean_object* v___x_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_apply_2(v_a_483_, v___x_484_, lean_box(0));
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 1);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_486_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_486_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 0);
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object* v_a_503_, lean_object* v___x_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(v_a_503_, v___x_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object* v_linter_507_, size_t v_sz_508_, size_t v_i_509_, lean_object* v_bs_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_lt(v_i_509_, v_sz_508_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v_linter_507_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_bs_510_);
return v___x_515_;
}
else
{
lean_object* v_toEnvLinter_516_; lean_object* v_test_517_; lean_object* v_v_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_toEnvLinter_516_ = lean_ctor_get(v_linter_507_, 0);
v_test_517_ = lean_ctor_get(v_toEnvLinter_516_, 0);
v_v_518_ = lean_array_uget(v_bs_510_, v_i_509_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_box(1);
lean_inc(v_v_518_);
lean_inc_ref(v_test_517_);
v___f_521_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed), 8, 4);
lean_closure_set(v___f_521_, 0, v___x_519_);
lean_closure_set(v___f_521_, 1, v___x_520_);
lean_closure_set(v___f_521_, 2, v_test_517_);
lean_closure_set(v___f_521_, 3, v_v_518_);
v___x_522_ = lean_box(0);
v___x_523_ = l_Lean_Core_wrapAsync___redArg(v___f_521_, v___x_522_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v_bs_x27_528_; lean_object* v___x_529_; size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = lean_box(0);
v___f_526_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_526_, 0, v_a_524_);
lean_closure_set(v___f_526_, 1, v___x_525_);
v___x_527_ = lean_io_as_task(v___f_526_, v___x_519_);
v_bs_x27_528_ = lean_array_uset(v_bs_510_, v_i_509_, v___x_519_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_v_518_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_509_, v___x_530_);
v___x_532_ = lean_array_uset(v_bs_x27_528_, v_i_509_, v___x_529_);
v_i_509_ = v___x_531_;
v_bs_510_ = v___x_532_;
goto _start;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_v_518_);
lean_dec_ref(v_bs_510_);
lean_dec_ref(v_linter_507_);
v_a_534_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_523_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_523_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object* v_linter_542_, lean_object* v_sz_543_, lean_object* v_i_544_, lean_object* v_bs_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_543_);
lean_dec(v_sz_543_);
v_i_boxed_550_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_linter_542_, v_sz_boxed_549_, v_i_boxed_550_, v_bs_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(lean_object* v_decls_552_, size_t v_sz_553_, size_t v_i_554_, lean_object* v_bs_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_554_, v_sz_553_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_bs_555_);
return v___x_560_;
}
else
{
lean_object* v_v_561_; lean_object* v___x_562_; lean_object* v_bs_x27_563_; lean_object* v_a_565_; lean_object* v___y_576_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_v_561_ = lean_array_uget(v_bs_555_, v_i_554_);
v___x_562_ = lean_unsigned_to_nat(0u);
v_bs_x27_563_ = lean_array_uset(v_bs_555_, v_i_554_, v___x_562_);
v___x_586_ = lean_array_get_size(v_decls_552_);
v___x_587_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_588_ = lean_nat_dec_lt(v___x_562_, v___x_586_);
if (v___x_588_ == 0)
{
v_a_565_ = v___x_587_;
goto v___jp_564_;
}
else
{
lean_object* v_name_589_; uint8_t v___x_590_; 
v_name_589_ = lean_ctor_get(v_v_561_, 1);
v___x_590_ = lean_nat_dec_le(v___x_586_, v___x_586_);
if (v___x_590_ == 0)
{
if (v___x_588_ == 0)
{
v_a_565_ = v___x_587_;
goto v___jp_564_;
}
else
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_591_ = ((size_t)0ULL);
v___x_592_ = lean_usize_of_nat(v___x_586_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_589_, v_decls_552_, v___x_591_, v___x_592_, v___x_587_, v___y_556_, v___y_557_);
v___y_576_ = v___x_593_;
goto v___jp_575_;
}
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_586_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_589_, v_decls_552_, v___x_594_, v___x_595_, v___x_587_, v___y_556_, v___y_557_);
v___y_576_ = v___x_596_;
goto v___jp_575_;
}
}
v___jp_564_:
{
size_t v_sz_566_; size_t v___x_567_; lean_object* v___x_568_; 
v_sz_566_ = lean_array_size(v_a_565_);
v___x_567_ = ((size_t)0ULL);
lean_inc(v_v_561_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_561_, v_sz_566_, v___x_567_, v_a_565_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_v_561_);
lean_ctor_set(v___x_570_, 1, v_a_569_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_554_, v___x_571_);
v___x_573_ = lean_array_uset(v_bs_x27_563_, v_i_554_, v___x_570_);
v_i_554_ = v___x_572_;
v_bs_555_ = v___x_573_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_563_);
lean_dec(v_v_561_);
return v___x_568_;
}
}
v___jp_575_:
{
if (lean_obj_tag(v___y_576_) == 0)
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v___y_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___y_576_);
v_a_565_ = v_a_577_;
goto v___jp_564_;
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v_bs_x27_563_);
lean_dec(v_v_561_);
v_a_578_ = lean_ctor_get(v___y_576_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___y_576_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___y_576_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___y_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object* v_decls_597_, lean_object* v_sz_598_, lean_object* v_i_599_, lean_object* v_bs_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
size_t v_sz_boxed_604_; size_t v_i_boxed_605_; lean_object* v_res_606_; 
v_sz_boxed_604_ = lean_unbox_usize(v_sz_598_);
lean_dec(v_sz_598_);
v_i_boxed_605_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_res_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_597_, v_sz_boxed_604_, v_i_boxed_605_, v_bs_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v_decls_597_);
return v_res_606_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_607_; uint64_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(1723u);
v___x_608_ = lean_uint64_of_nat(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
return v_x_609_;
}
else
{
lean_object* v_key_611_; lean_object* v_value_612_; lean_object* v_tail_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_639_; 
v_key_611_ = lean_ctor_get(v_x_610_, 0);
v_value_612_ = lean_ctor_get(v_x_610_, 1);
v_tail_613_ = lean_ctor_get(v_x_610_, 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_610_);
if (v_isSharedCheck_639_ == 0)
{
v___x_615_ = v_x_610_;
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_tail_613_);
lean_inc(v_value_612_);
lean_inc(v_key_611_);
lean_dec(v_x_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; uint64_t v___y_619_; 
v___x_617_ = lean_array_get_size(v_x_609_);
if (lean_obj_tag(v_key_611_) == 0)
{
uint64_t v___x_637_; 
v___x_637_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_619_ = v___x_637_;
goto v___jp_618_;
}
else
{
uint64_t v_hash_638_; 
v_hash_638_ = lean_ctor_get_uint64(v_key_611_, sizeof(void*)*2);
v___y_619_ = v_hash_638_;
goto v___jp_618_;
}
v___jp_618_:
{
uint64_t v___x_620_; uint64_t v___x_621_; uint64_t v_fold_622_; uint64_t v___x_623_; uint64_t v___x_624_; uint64_t v___x_625_; size_t v___x_626_; size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_620_ = 32ULL;
v___x_621_ = lean_uint64_shift_right(v___y_619_, v___x_620_);
v_fold_622_ = lean_uint64_xor(v___y_619_, v___x_621_);
v___x_623_ = 16ULL;
v___x_624_ = lean_uint64_shift_right(v_fold_622_, v___x_623_);
v___x_625_ = lean_uint64_xor(v_fold_622_, v___x_624_);
v___x_626_ = lean_uint64_to_usize(v___x_625_);
v___x_627_ = lean_usize_of_nat(v___x_617_);
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_sub(v___x_627_, v___x_628_);
v___x_630_ = lean_usize_land(v___x_626_, v___x_629_);
v___x_631_ = lean_array_uget_borrowed(v_x_609_, v___x_630_);
lean_inc(v___x_631_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 2, v___x_631_);
v___x_633_ = v___x_615_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_key_611_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_value_612_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v___x_631_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; 
v___x_634_ = lean_array_uset(v_x_609_, v___x_630_, v___x_633_);
v_x_609_ = v___x_634_;
v_x_610_ = v_tail_613_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_640_, lean_object* v_source_641_, lean_object* v_target_642_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_array_get_size(v_source_641_);
v___x_644_ = lean_nat_dec_lt(v_i_640_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_source_641_);
lean_dec(v_i_640_);
return v_target_642_;
}
else
{
lean_object* v_es_645_; lean_object* v___x_646_; lean_object* v_source_647_; lean_object* v_target_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_es_645_ = lean_array_fget(v_source_641_, v_i_640_);
v___x_646_ = lean_box(0);
v_source_647_ = lean_array_fset(v_source_641_, v_i_640_, v___x_646_);
v_target_648_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_target_642_, v_es_645_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_i_640_, v___x_649_);
lean_dec(v_i_640_);
v_i_640_ = v___x_650_;
v_source_641_ = v_source_647_;
v_target_642_ = v_target_648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object* v_data_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_nbuckets_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_653_ = lean_array_get_size(v_data_652_);
v___x_654_ = lean_unsigned_to_nat(2u);
v_nbuckets_655_ = lean_nat_mul(v___x_653_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_box(0);
v___x_658_ = lean_mk_array(v_nbuckets_655_, v___x_657_);
v___x_659_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v___x_656_, v_data_652_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object* v_a_660_, lean_object* v_b_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_dec(v_b_661_);
lean_dec(v_a_660_);
return v_x_662_;
}
else
{
lean_object* v_key_663_; lean_object* v_value_664_; lean_object* v_tail_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_677_; 
v_key_663_ = lean_ctor_get(v_x_662_, 0);
v_value_664_ = lean_ctor_get(v_x_662_, 1);
v_tail_665_ = lean_ctor_get(v_x_662_, 2);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_662_);
if (v_isSharedCheck_677_ == 0)
{
v___x_667_ = v_x_662_;
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_tail_665_);
lean_inc(v_value_664_);
lean_inc(v_key_663_);
lean_dec(v_x_662_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; 
v___x_669_ = lean_name_eq(v_key_663_, v_a_660_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_660_, v_b_661_, v_tail_665_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 2, v___x_670_);
v___x_672_ = v___x_667_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_key_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_value_664_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v___x_675_; 
lean_dec(v_value_664_);
lean_dec(v_key_663_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v_b_661_);
lean_ctor_set(v___x_667_, 0, v_a_660_);
v___x_675_ = v___x_667_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_660_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_b_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_tail_665_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 0;
return v___x_680_;
}
else
{
lean_object* v_key_681_; lean_object* v_tail_682_; uint8_t v___x_683_; 
v_key_681_ = lean_ctor_get(v_x_679_, 0);
v_tail_682_ = lean_ctor_get(v_x_679_, 2);
v___x_683_ = lean_name_eq(v_key_681_, v_a_678_);
if (v___x_683_ == 0)
{
v_x_679_ = v_tail_682_;
goto _start;
}
else
{
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_685_, lean_object* v_x_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_685_, v_x_686_);
lean_dec(v_x_686_);
lean_dec(v_a_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object* v_m_689_, lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_size_692_; lean_object* v_buckets_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_739_; 
v_size_692_ = lean_ctor_get(v_m_689_, 0);
v_buckets_693_ = lean_ctor_get(v_m_689_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_m_689_);
if (v_isSharedCheck_739_ == 0)
{
v___x_695_ = v_m_689_;
v_isShared_696_ = v_isSharedCheck_739_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_buckets_693_);
lean_inc(v_size_692_);
lean_dec(v_m_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_739_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; uint64_t v___y_699_; 
v___x_697_ = lean_array_get_size(v_buckets_693_);
if (lean_obj_tag(v_a_690_) == 0)
{
uint64_t v___x_737_; 
v___x_737_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_699_ = v___x_737_;
goto v___jp_698_;
}
else
{
uint64_t v_hash_738_; 
v_hash_738_ = lean_ctor_get_uint64(v_a_690_, sizeof(void*)*2);
v___y_699_ = v_hash_738_;
goto v___jp_698_;
}
v___jp_698_:
{
uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v_fold_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; lean_object* v_bkt_711_; uint8_t v___x_712_; 
v___x_700_ = 32ULL;
v___x_701_ = lean_uint64_shift_right(v___y_699_, v___x_700_);
v_fold_702_ = lean_uint64_xor(v___y_699_, v___x_701_);
v___x_703_ = 16ULL;
v___x_704_ = lean_uint64_shift_right(v_fold_702_, v___x_703_);
v___x_705_ = lean_uint64_xor(v_fold_702_, v___x_704_);
v___x_706_ = lean_uint64_to_usize(v___x_705_);
v___x_707_ = lean_usize_of_nat(v___x_697_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_sub(v___x_707_, v___x_708_);
v___x_710_ = lean_usize_land(v___x_706_, v___x_709_);
v_bkt_711_ = lean_array_uget_borrowed(v_buckets_693_, v___x_710_);
v___x_712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_690_, v_bkt_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v_size_x27_714_; lean_object* v___x_715_; lean_object* v_buckets_x27_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v_size_x27_714_ = lean_nat_add(v_size_692_, v___x_713_);
lean_dec(v_size_692_);
lean_inc(v_bkt_711_);
v___x_715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_715_, 0, v_a_690_);
lean_ctor_set(v___x_715_, 1, v_b_691_);
lean_ctor_set(v___x_715_, 2, v_bkt_711_);
v_buckets_x27_716_ = lean_array_uset(v_buckets_693_, v___x_710_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(4u);
v___x_718_ = lean_nat_mul(v_size_x27_714_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(3u);
v___x_720_ = lean_nat_div(v___x_718_, v___x_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_array_get_size(v_buckets_x27_716_);
v___x_722_ = lean_nat_dec_le(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
if (v___x_722_ == 0)
{
lean_object* v_val_723_; lean_object* v___x_725_; 
v_val_723_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_buckets_x27_716_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_val_723_);
lean_ctor_set(v___x_695_, 0, v_size_x27_714_);
v___x_725_ = v___x_695_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_size_x27_714_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_val_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_728_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_buckets_x27_716_);
lean_ctor_set(v___x_695_, 0, v_size_x27_714_);
v___x_728_ = v___x_695_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_size_x27_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_buckets_x27_716_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v___x_730_; lean_object* v_buckets_x27_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
lean_inc(v_bkt_711_);
v___x_730_ = lean_box(0);
v_buckets_x27_731_ = lean_array_uset(v_buckets_693_, v___x_710_, v___x_730_);
v___x_732_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_690_, v_b_691_, v_bkt_711_);
v___x_733_ = lean_array_uset(v_buckets_x27_731_, v___x_710_, v___x_732_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___x_733_);
v___x_735_ = v___x_695_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_size_692_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object* v_as_743_, size_t v_sz_744_, size_t v_i_745_, lean_object* v_b_746_){
_start:
{
lean_object* v_a_749_; uint8_t v___x_753_; 
v___x_753_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_b_746_);
return v___x_754_;
}
else
{
lean_object* v_a_755_; lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_773_; 
v_a_755_ = lean_array_uget(v_as_743_, v_i_745_);
v_fst_756_ = lean_ctor_get(v_a_755_, 0);
v_snd_757_ = lean_ctor_get(v_a_755_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_773_ == 0)
{
v___x_759_ = v_a_755_;
v_isShared_760_ = v_isSharedCheck_773_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_756_);
lean_dec(v_a_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_773_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_val_762_; lean_object* v___x_764_; 
v___x_764_ = lean_task_get_own(v_snd_757_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
v___x_766_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1);
v___x_767_ = l_Lean_Exception_toMessageData(v_a_765_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 7);
lean_ctor_set(v___x_759_, 1, v___x_767_);
lean_ctor_set(v___x_759_, 0, v___x_766_);
v___x_769_ = v___x_759_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
v_val_762_ = v___x_769_;
goto v___jp_761_;
}
}
else
{
lean_object* v_a_771_; 
lean_del_object(v___x_759_);
v_a_771_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_764_);
if (lean_obj_tag(v_a_771_) == 1)
{
lean_object* v_val_772_; 
v_val_772_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v_a_771_);
v_val_762_ = v_val_772_;
goto v___jp_761_;
}
else
{
lean_dec(v_a_771_);
lean_dec(v_fst_756_);
v_a_749_ = v_b_746_;
goto v___jp_748_;
}
}
v___jp_761_:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_746_, v_fst_756_, v_val_762_);
v_a_749_ = v___x_763_;
goto v___jp_748_;
}
}
}
v___jp_748_:
{
size_t v___x_750_; size_t v___x_751_; 
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_745_, v___x_750_);
v_i_745_ = v___x_751_;
v_b_746_ = v_a_749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object* v_as_774_, lean_object* v_sz_775_, lean_object* v_i_776_, lean_object* v_b_777_, lean_object* v___y_778_){
_start:
{
size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_sz_boxed_779_ = lean_unbox_usize(v_sz_775_);
lean_dec(v_sz_775_);
v_i_boxed_780_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_774_, v_sz_boxed_779_, v_i_boxed_780_, v_b_777_);
lean_dec_ref(v_as_774_);
return v_res_781_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_box(0);
v___x_783_ = lean_unsigned_to_nat(16u);
v___x_784_ = lean_mk_array(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(size_t v_sz_788_, size_t v_i_789_, lean_object* v_bs_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = lean_usize_dec_lt(v_i_789_, v_sz_788_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_bs_790_);
return v___x_795_;
}
else
{
lean_object* v_v_796_; lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_824_; 
v_v_796_ = lean_array_uget(v_bs_790_, v_i_789_);
v_fst_797_ = lean_ctor_get(v_v_796_, 0);
v_snd_798_ = lean_ctor_get(v_v_796_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_v_796_);
if (v_isSharedCheck_824_ == 0)
{
v___x_800_ = v_v_796_;
v_isShared_801_ = v_isSharedCheck_824_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_inc(v_fst_797_);
lean_dec(v_v_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_824_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v_sz_804_ = lean_array_size(v_snd_798_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_snd_798_, v_sz_804_, v___x_805_, v___x_803_);
lean_dec(v_snd_798_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_bs_x27_808_; lean_object* v___x_810_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v_bs_x27_808_ = lean_array_uset(v_bs_790_, v_i_789_, v___x_802_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_a_807_);
v___x_810_ = v___x_800_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fst_797_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_a_807_);
v___x_810_ = v_reuseFailAlloc_815_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_add(v_i_789_, v___x_811_);
v___x_813_ = lean_array_uset(v_bs_x27_808_, v_i_789_, v___x_810_);
v_i_789_ = v___x_812_;
v_bs_790_ = v___x_813_;
goto _start;
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_800_);
lean_dec(v_fst_797_);
lean_dec_ref(v_bs_790_);
v_a_816_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_806_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_806_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___boxed(lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_bs_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
size_t v_sz_boxed_831_; size_t v_i_boxed_832_; lean_object* v_res_833_; 
v_sz_boxed_831_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_832_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_boxed_831_, v_i_boxed_832_, v_bs_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object* v_decls_834_, lean_object* v_linters_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
size_t v_sz_839_; size_t v___x_840_; lean_object* v___x_841_; 
v_sz_839_ = lean_array_size(v_linters_835_);
v___x_840_ = ((size_t)0ULL);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_834_, v_sz_839_, v___x_840_, v_linters_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; size_t v_sz_843_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
v_sz_843_ = lean_array_size(v_a_842_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_843_, v___x_840_, v_a_842_, v_a_836_, v_a_837_);
return v___x_844_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_841_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object* v_decls_853_, lean_object* v_linters_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Linter_EnvLinter_lintCore(v_decls_853_, v_linters_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec_ref(v_decls_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object* v_00_u03b2_859_, lean_object* v_m_860_, lean_object* v_a_861_, lean_object* v_b_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_m_860_, v_a_861_, v_b_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object* v_as_864_, size_t v_sz_865_, size_t v_i_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_864_, v_sz_865_, v_i_866_, v_b_867_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object* v_as_872_, lean_object* v_sz_873_, lean_object* v_i_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
size_t v_sz_boxed_879_; size_t v_i_boxed_880_; lean_object* v_res_881_; 
v_sz_boxed_879_ = lean_unbox_usize(v_sz_873_);
lean_dec(v_sz_873_);
v_i_boxed_880_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(v_as_872_, v_sz_boxed_879_, v_i_boxed_880_, v_b_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_as_872_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object* v_linter_882_, lean_object* v_decl_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_882_, v_decl_883_, v___y_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object* v_linter_888_, lean_object* v_decl_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v_linter_888_, v_decl_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v_linter_888_);
return v_res_893_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object* v_00_u03b2_894_, lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_898_, lean_object* v_a_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(v_00_u03b2_898_, v_a_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_a_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object* v_00_u03b2_903_, lean_object* v_data_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_data_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object* v_00_u03b2_906_, lean_object* v_a_907_, lean_object* v_b_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_907_, v_b_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_911_, lean_object* v_i_912_, lean_object* v_source_913_, lean_object* v_target_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v_i_912_, v_source_913_, v_target_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_x_917_, v_x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object* v_a_920_, lean_object* v_fallback_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_inc(v_fallback_921_);
return v_fallback_921_;
}
else
{
lean_object* v_key_923_; lean_object* v_value_924_; lean_object* v_tail_925_; uint8_t v___x_926_; 
v_key_923_ = lean_ctor_get(v_x_922_, 0);
v_value_924_ = lean_ctor_get(v_x_922_, 1);
v_tail_925_ = lean_ctor_get(v_x_922_, 2);
v___x_926_ = lean_name_eq(v_key_923_, v_a_920_);
if (v___x_926_ == 0)
{
v_x_922_ = v_tail_925_;
goto _start;
}
else
{
lean_inc(v_value_924_);
return v_value_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object* v_a_928_, lean_object* v_fallback_929_, lean_object* v_x_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_928_, v_fallback_929_, v_x_930_);
lean_dec(v_x_930_);
lean_dec(v_fallback_929_);
lean_dec(v_a_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object* v_m_932_, lean_object* v_a_933_, lean_object* v_fallback_934_){
_start:
{
lean_object* v_buckets_935_; lean_object* v___x_936_; uint64_t v___y_938_; 
v_buckets_935_ = lean_ctor_get(v_m_932_, 1);
v___x_936_ = lean_array_get_size(v_buckets_935_);
if (lean_obj_tag(v_a_933_) == 0)
{
uint64_t v___x_952_; 
v___x_952_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_938_ = v___x_952_;
goto v___jp_937_;
}
else
{
uint64_t v_hash_953_; 
v_hash_953_ = lean_ctor_get_uint64(v_a_933_, sizeof(void*)*2);
v___y_938_ = v_hash_953_;
goto v___jp_937_;
}
v___jp_937_:
{
uint64_t v___x_939_; uint64_t v___x_940_; uint64_t v_fold_941_; uint64_t v___x_942_; uint64_t v___x_943_; uint64_t v___x_944_; size_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_939_ = 32ULL;
v___x_940_ = lean_uint64_shift_right(v___y_938_, v___x_939_);
v_fold_941_ = lean_uint64_xor(v___y_938_, v___x_940_);
v___x_942_ = 16ULL;
v___x_943_ = lean_uint64_shift_right(v_fold_941_, v___x_942_);
v___x_944_ = lean_uint64_xor(v_fold_941_, v___x_943_);
v___x_945_ = lean_uint64_to_usize(v___x_944_);
v___x_946_ = lean_usize_of_nat(v___x_936_);
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_sub(v___x_946_, v___x_947_);
v___x_949_ = lean_usize_land(v___x_945_, v___x_948_);
v___x_950_ = lean_array_uget_borrowed(v_buckets_935_, v___x_949_);
v___x_951_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_933_, v_fallback_934_, v___x_950_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object* v_m_954_, lean_object* v_a_955_, lean_object* v_fallback_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_954_, v_a_955_, v_fallback_956_);
lean_dec(v_fallback_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_m_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object* v_a_958_, lean_object* v_hi_959_, lean_object* v_pivot_960_, lean_object* v_as_961_, lean_object* v_i_962_, lean_object* v_k_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_lt(v_k_963_, v_hi_959_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_k_963_);
v___x_965_ = lean_array_fswap(v_as_961_, v_i_962_, v_hi_959_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_i_962_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v_fst_968_; lean_object* v_fst_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_967_ = lean_array_fget_borrowed(v_as_961_, v_k_963_);
v_fst_968_ = lean_ctor_get(v___x_967_, 0);
v_fst_969_ = lean_ctor_get(v_pivot_960_, 0);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_958_, v_fst_968_, v___x_970_);
v___x_972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_958_, v_fst_969_, v___x_970_);
v___x_973_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
lean_dec(v___x_972_);
lean_dec(v___x_971_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_add(v_k_963_, v___x_974_);
lean_dec(v_k_963_);
v_k_963_ = v___x_975_;
goto _start;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_array_fswap(v_as_961_, v_i_962_, v_k_963_);
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = lean_nat_add(v_i_962_, v___x_978_);
lean_dec(v_i_962_);
v___x_980_ = lean_nat_add(v_k_963_, v___x_978_);
lean_dec(v_k_963_);
v_as_961_ = v___x_977_;
v_i_962_ = v___x_979_;
v_k_963_ = v___x_980_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object* v_a_982_, lean_object* v_hi_983_, lean_object* v_pivot_984_, lean_object* v_as_985_, lean_object* v_i_986_, lean_object* v_k_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_982_, v_hi_983_, v_pivot_984_, v_as_985_, v_i_986_, v_k_987_);
lean_dec_ref(v_pivot_984_);
lean_dec(v_hi_983_);
lean_dec_ref(v_a_982_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object* v_a_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v_fst_992_; lean_object* v_fst_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_fst_992_ = lean_ctor_get(v_x_990_, 0);
v_fst_993_ = lean_ctor_get(v_x_991_, 0);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_989_, v_fst_992_, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_989_, v_fst_993_, v___x_994_);
v___x_997_ = lean_nat_dec_lt(v___x_995_, v___x_996_);
lean_dec(v___x_996_);
lean_dec(v___x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object* v_a_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_998_, v_x_999_, v_x_1000_);
lean_dec_ref(v_x_1000_);
lean_dec_ref(v_x_999_);
lean_dec_ref(v_a_998_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object* v_a_1003_, lean_object* v_n_1004_, lean_object* v_as_1005_, lean_object* v_lo_1006_, lean_object* v_hi_1007_){
_start:
{
lean_object* v___y_1009_; uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_lt(v_lo_1006_, v_hi_1007_);
if (v___x_1019_ == 0)
{
lean_dec(v_lo_1006_);
return v_as_1005_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_mid_1022_; lean_object* v___y_1024_; lean_object* v___y_1030_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1020_ = lean_nat_add(v_lo_1006_, v_hi_1007_);
v___x_1021_ = lean_unsigned_to_nat(1u);
v_mid_1022_ = lean_nat_shiftr(v___x_1020_, v___x_1021_);
lean_dec(v___x_1020_);
v___x_1035_ = lean_array_fget_borrowed(v_as_1005_, v_mid_1022_);
v___x_1036_ = lean_array_fget_borrowed(v_as_1005_, v_lo_1006_);
v___x_1037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1003_, v___x_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
v___y_1030_ = v_as_1005_;
goto v___jp_1029_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_array_fswap(v_as_1005_, v_lo_1006_, v_mid_1022_);
v___y_1030_ = v___x_1038_;
goto v___jp_1029_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_array_fget_borrowed(v___y_1024_, v_mid_1022_);
v___x_1026_ = lean_array_fget_borrowed(v___y_1024_, v_hi_1007_);
v___x_1027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1003_, v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_dec(v_mid_1022_);
v___y_1009_ = v___y_1024_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_array_fswap(v___y_1024_, v_mid_1022_, v_hi_1007_);
lean_dec(v_mid_1022_);
v___y_1009_ = v___x_1028_;
goto v___jp_1008_;
}
}
v___jp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = lean_array_fget_borrowed(v___y_1030_, v_hi_1007_);
v___x_1032_ = lean_array_fget_borrowed(v___y_1030_, v_lo_1006_);
v___x_1033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1003_, v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
v___y_1024_ = v___y_1030_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_array_fswap(v___y_1030_, v_lo_1006_, v_hi_1007_);
v___y_1024_ = v___x_1034_;
goto v___jp_1023_;
}
}
}
v___jp_1008_:
{
lean_object* v_pivot_1010_; lean_object* v___x_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; uint8_t v___x_1014_; 
v_pivot_1010_ = lean_array_fget(v___y_1009_, v_hi_1007_);
lean_inc_n(v_lo_1006_, 2);
v___x_1011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1003_, v_hi_1007_, v_pivot_1010_, v___y_1009_, v_lo_1006_, v_lo_1006_);
lean_dec(v_pivot_1010_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_fst_1012_);
v_snd_1013_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_snd_1013_);
lean_dec_ref(v___x_1011_);
v___x_1014_ = lean_nat_dec_le(v_hi_1007_, v_fst_1012_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1003_, v_n_1004_, v_snd_1013_, v_lo_1006_, v_fst_1012_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_fst_1012_, v___x_1016_);
lean_dec(v_fst_1012_);
v_as_1005_ = v___x_1015_;
v_lo_1006_ = v___x_1017_;
goto _start;
}
else
{
lean_dec(v_fst_1012_);
lean_dec(v_lo_1006_);
return v_snd_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object* v_a_1039_, lean_object* v_n_1040_, lean_object* v_as_1041_, lean_object* v_lo_1042_, lean_object* v_hi_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1039_, v_n_1040_, v_as_1041_, v_lo_1042_, v_hi_1043_);
lean_dec(v_hi_1043_);
lean_dec(v_n_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object* v_declName_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v_env_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = lean_st_ref_get(v___y_1046_);
v_env_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_ref(v_env_1049_);
lean_dec(v___x_1048_);
v___x_1050_ = l_Lean_isRecCore(v_env_1049_, v_declName_1045_);
v___x_1051_ = lean_box(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1053_, v___y_1054_);
lean_dec(v___y_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object* v_declName_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v_env_1061_; lean_object* v___x_1062_; lean_object* v_env_1063_; lean_object* v___x_1064_; lean_object* v_toEnvExtension_1065_; lean_object* v_asyncMode_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1060_ = lean_st_ref_get(v___y_1058_);
v_env_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc_ref(v_env_1061_);
lean_dec(v___x_1060_);
v___x_1062_ = lean_st_ref_get(v___y_1058_);
v_env_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_ref(v_env_1063_);
lean_dec(v___x_1062_);
v___x_1064_ = l_Lean_declRangeExt;
v_toEnvExtension_1065_ = lean_ctor_get(v___x_1064_, 0);
v_asyncMode_1066_ = lean_ctor_get(v_toEnvExtension_1065_, 2);
v___x_1067_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1068_ = 0;
lean_inc(v_declName_1057_);
v___x_1069_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1067_, v___x_1064_, v_env_1061_, v_declName_1057_, v_asyncMode_1066_, v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = 1;
v___x_1071_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1067_, v___x_1064_, v_env_1063_, v_declName_1057_, v_asyncMode_1066_, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; 
lean_dec_ref(v_env_1063_);
lean_dec(v_declName_1057_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1069_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1074_, v___y_1075_);
lean_dec(v___y_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object* v_declName_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_ranges_1083_; lean_object* v___x_1089_; lean_object* v_env_1090_; lean_object* v___x_1091_; lean_object* v_a_1092_; uint8_t v___y_1098_; uint8_t v___x_1102_; 
v___x_1089_ = lean_st_ref_get(v___y_1080_);
v_env_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref_n(v_env_1090_, 2);
lean_dec(v___x_1089_);
lean_inc_n(v_declName_1078_, 2);
v___x_1091_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1078_, v___y_1080_);
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v___x_1102_ = l_Lean_isAuxRecursor(v_env_1090_, v_declName_1078_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; 
lean_inc(v_declName_1078_);
v___x_1103_ = l_Lean_isNoConfusion(v_env_1090_, v_declName_1078_);
v___y_1098_ = v___x_1103_;
goto v___jp_1097_;
}
else
{
lean_dec_ref(v_env_1090_);
v___y_1098_ = v___x_1102_;
goto v___jp_1097_;
}
v___jp_1082_:
{
if (lean_obj_tag(v_ranges_1083_) == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1084_ = l_Lean_builtinDeclRanges;
v___x_1085_ = lean_st_ref_get(v___x_1084_);
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1085_, v_declName_1078_);
lean_dec(v_declName_1078_);
lean_dec(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_declName_1078_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_ranges_1083_);
return v___x_1088_;
}
}
v___jp_1093_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_a_1096_; 
v___x_1094_ = l_Lean_Name_getPrefix(v_declName_1078_);
v___x_1095_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v___x_1094_, v___y_1080_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref(v___x_1095_);
v_ranges_1083_ = v_a_1096_;
goto v___jp_1082_;
}
v___jp_1097_:
{
if (v___y_1098_ == 0)
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_unbox(v_a_1092_);
lean_dec(v_a_1092_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v_a_1101_; 
lean_inc(v_declName_1078_);
v___x_1100_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1078_, v___y_1080_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v___x_1100_);
v_ranges_1083_ = v_a_1101_;
goto v___jp_1082_;
}
else
{
goto v___jp_1093_;
}
}
else
{
lean_dec(v_a_1092_);
goto v___jp_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object* v_declName_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object* v_as_1109_, size_t v_sz_1110_, size_t v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1111_, v_sz_1110_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_b_1112_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v_fst_1119_; lean_object* v___x_1120_; 
v_a_1118_ = lean_array_uget_borrowed(v_as_1109_, v_i_1111_);
v_fst_1119_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_fst_1119_);
v___x_1120_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_fst_1119_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v_a_1123_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
if (lean_obj_tag(v_a_1121_) == 1)
{
lean_object* v_val_1127_; lean_object* v_range_1128_; lean_object* v_pos_1129_; lean_object* v_line_1130_; lean_object* v___x_1131_; 
v_val_1127_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_val_1127_);
lean_dec_ref(v_a_1121_);
v_range_1128_ = lean_ctor_get(v_val_1127_, 0);
lean_inc_ref(v_range_1128_);
lean_dec(v_val_1127_);
v_pos_1129_ = lean_ctor_get(v_range_1128_, 0);
lean_inc_ref(v_pos_1129_);
lean_dec_ref(v_range_1128_);
v_line_1130_ = lean_ctor_get(v_pos_1129_, 0);
lean_inc(v_line_1130_);
lean_dec_ref(v_pos_1129_);
lean_inc(v_fst_1119_);
v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_1112_, v_fst_1119_, v_line_1130_);
v_a_1123_ = v___x_1131_;
goto v___jp_1122_;
}
else
{
lean_dec(v_a_1121_);
v_a_1123_ = v_b_1112_;
goto v___jp_1122_;
}
v___jp_1122_:
{
size_t v___x_1124_; size_t v___x_1125_; 
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1111_, v___x_1124_);
v_i_1111_ = v___x_1125_;
v_b_1112_ = v_a_1123_;
goto _start;
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_b_1112_);
v_a_1132_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1120_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1120_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object* v_as_1140_, lean_object* v_sz_1141_, lean_object* v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
size_t v_sz_boxed_1147_; size_t v_i_boxed_1148_; lean_object* v_res_1149_; 
v_sz_boxed_1147_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1148_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1140_, v_sz_boxed_1147_, v_i_boxed_1148_, v_b_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v_as_1140_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1151_) == 0)
{
return v_x_1150_;
}
else
{
lean_object* v_key_1152_; lean_object* v_value_1153_; lean_object* v_tail_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_key_1152_ = lean_ctor_get(v_x_1151_, 0);
v_value_1153_ = lean_ctor_get(v_x_1151_, 1);
v_tail_1154_ = lean_ctor_get(v_x_1151_, 2);
lean_inc(v_value_1153_);
lean_inc(v_key_1152_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_key_1152_);
lean_ctor_set(v___x_1155_, 1, v_value_1153_);
v___x_1156_ = lean_array_push(v_x_1150_, v___x_1155_);
v_x_1150_ = v___x_1156_;
v_x_1151_ = v_tail_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1158_, v_x_1159_);
lean_dec(v_x_1159_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object* v_as_1161_, size_t v_i_1162_, size_t v_stop_1163_, lean_object* v_b_1164_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_eq(v_i_1162_, v_stop_1163_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; 
v___x_1166_ = lean_array_uget_borrowed(v_as_1161_, v_i_1162_);
v___x_1167_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_b_1164_, v___x_1166_);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_add(v_i_1162_, v___x_1168_);
v_i_1162_ = v___x_1169_;
v_b_1164_ = v___x_1167_;
goto _start;
}
else
{
return v_b_1164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object* v_as_1171_, lean_object* v_i_1172_, lean_object* v_stop_1173_, lean_object* v_b_1174_){
_start:
{
size_t v_i_boxed_1175_; size_t v_stop_boxed_1176_; lean_object* v_res_1177_; 
v_i_boxed_1175_ = lean_unbox_usize(v_i_1172_);
lean_dec(v_i_1172_);
v_stop_boxed_1176_ = lean_unbox_usize(v_stop_1173_);
lean_dec(v_stop_1173_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1171_, v_i_boxed_1175_, v_stop_boxed_1176_, v_b_1174_);
lean_dec_ref(v_as_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object* v_results_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v_size_1197_; lean_object* v_buckets_1198_; lean_object* v___x_1199_; lean_object* v_key_1200_; lean_object* v___y_1202_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_size_1197_ = lean_ctor_get(v_results_1178_, 0);
v_buckets_1198_ = lean_ctor_get(v_results_1178_, 1);
v___x_1199_ = lean_unsigned_to_nat(0u);
v_key_1200_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_1227_ = lean_mk_empty_array_with_capacity(v_size_1197_);
v___x_1228_ = lean_array_get_size(v_buckets_1198_);
v___x_1229_ = lean_nat_dec_lt(v___x_1199_, v___x_1228_);
if (v___x_1229_ == 0)
{
v___y_1202_ = v___x_1227_;
goto v___jp_1201_;
}
else
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_le(v___x_1228_, v___x_1228_);
if (v___x_1230_ == 0)
{
if (v___x_1229_ == 0)
{
v___y_1202_ = v___x_1227_;
goto v___jp_1201_;
}
else
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = lean_usize_of_nat(v___x_1228_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1198_, v___x_1231_, v___x_1232_, v___x_1227_);
v___y_1202_ = v___x_1233_;
goto v___jp_1201_;
}
}
else
{
size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = ((size_t)0ULL);
v___x_1235_ = lean_usize_of_nat(v___x_1228_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1198_, v___x_1234_, v___x_1235_, v___x_1227_);
v___y_1202_ = v___x_1236_;
goto v___jp_1201_;
}
}
v___jp_1182_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v___y_1186_, v___y_1184_, v___y_1185_, v___y_1183_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1186_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
v___jp_1190_:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_nat_dec_le(v___y_1195_, v___y_1194_);
if (v___x_1196_ == 0)
{
lean_dec(v___y_1194_);
lean_inc(v___y_1195_);
v___y_1183_ = v___y_1195_;
v___y_1184_ = v___y_1191_;
v___y_1185_ = v___y_1193_;
v___y_1186_ = v___y_1192_;
v___y_1187_ = v___y_1195_;
goto v___jp_1182_;
}
else
{
v___y_1183_ = v___y_1195_;
v___y_1184_ = v___y_1191_;
v___y_1185_ = v___y_1193_;
v___y_1186_ = v___y_1192_;
v___y_1187_ = v___y_1194_;
goto v___jp_1182_;
}
}
v___jp_1201_:
{
size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v_sz_1203_ = lean_array_size(v___y_1202_);
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v___y_1202_, v_sz_1203_, v___x_1204_, v_key_1200_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1218_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_array_get_size(v___y_1202_);
v___x_1211_ = lean_nat_dec_eq(v___x_1210_, v___x_1199_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
lean_del_object(v___x_1208_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_sub(v___x_1210_, v___x_1212_);
v___x_1214_ = lean_nat_dec_le(v___x_1199_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_inc(v___x_1213_);
v___y_1191_ = v___x_1210_;
v___y_1192_ = v_a_1206_;
v___y_1193_ = v___y_1202_;
v___y_1194_ = v___x_1213_;
v___y_1195_ = v___x_1213_;
goto v___jp_1190_;
}
else
{
v___y_1191_ = v___x_1210_;
v___y_1192_ = v_a_1206_;
v___y_1193_ = v___y_1202_;
v___y_1194_ = v___x_1213_;
v___y_1195_ = v___x_1199_;
goto v___jp_1190_;
}
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___y_1202_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___y_1202_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v___y_1202_);
v_a_1219_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1205_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1205_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object* v_results_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec_ref(v_results_1237_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object* v_00_u03b1_1242_, lean_object* v_results_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1243_, v_a_1244_, v_a_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_results_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Linter_EnvLinter_sortResults(v_00_u03b1_1248_, v_results_1249_, v_a_1250_, v_a_1251_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec_ref(v_results_1249_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object* v_declName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1254_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object* v_declName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(v_declName_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object* v_declName_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1264_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object* v_declName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(v_declName_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object* v_00_u03b1_1274_, lean_object* v_as_1275_, size_t v_sz_1276_, size_t v_i_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1275_, v_sz_1276_, v_i_1277_, v_b_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_as_1284_, lean_object* v_sz_1285_, lean_object* v_i_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
size_t v_sz_boxed_1291_; size_t v_i_boxed_1292_; lean_object* v_res_1293_; 
v_sz_boxed_1291_ = lean_unbox_usize(v_sz_1285_);
lean_dec(v_sz_1285_);
v_i_boxed_1292_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_res_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(v_00_u03b1_1283_, v_as_1284_, v_sz_boxed_1291_, v_i_boxed_1292_, v_b_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v_as_1284_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object* v_00_u03b2_1294_, lean_object* v_m_1295_, lean_object* v_a_1296_, lean_object* v_fallback_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1295_, v_a_1296_, v_fallback_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object* v_00_u03b2_1299_, lean_object* v_m_1300_, lean_object* v_a_1301_, lean_object* v_fallback_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(v_00_u03b2_1299_, v_m_1300_, v_a_1301_, v_fallback_1302_);
lean_dec(v_fallback_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_m_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object* v_00_u03b1_1304_, lean_object* v_a_1305_, lean_object* v_n_1306_, lean_object* v_as_1307_, lean_object* v_lo_1308_, lean_object* v_hi_1309_, lean_object* v_w_1310_, lean_object* v_hlo_1311_, lean_object* v_hhi_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1305_, v_n_1306_, v_as_1307_, v_lo_1308_, v_hi_1309_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_a_1315_, lean_object* v_n_1316_, lean_object* v_as_1317_, lean_object* v_lo_1318_, lean_object* v_hi_1319_, lean_object* v_w_1320_, lean_object* v_hlo_1321_, lean_object* v_hhi_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(v_00_u03b1_1314_, v_a_1315_, v_n_1316_, v_as_1317_, v_lo_1318_, v_hi_1319_, v_w_1320_, v_hlo_1321_, v_hhi_1322_);
lean_dec(v_hi_1319_);
lean_dec(v_n_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object* v_00_u03b1_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1325_, v_x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(v_00_u03b1_1328_, v_x_1329_, v_x_1330_);
lean_dec(v_x_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object* v_00_u03b1_1332_, lean_object* v_as_1333_, size_t v_i_1334_, size_t v_stop_1335_, lean_object* v_b_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1333_, v_i_1334_, v_stop_1335_, v_b_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_as_1339_, lean_object* v_i_1340_, lean_object* v_stop_1341_, lean_object* v_b_1342_){
_start:
{
size_t v_i_boxed_1343_; size_t v_stop_boxed_1344_; lean_object* v_res_1345_; 
v_i_boxed_1343_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_stop_boxed_1344_ = lean_unbox_usize(v_stop_1341_);
lean_dec(v_stop_1341_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(v_00_u03b1_1338_, v_as_1339_, v_i_boxed_1343_, v_stop_boxed_1344_, v_b_1342_);
lean_dec_ref(v_as_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object* v_00_u03b2_1346_, lean_object* v_a_1347_, lean_object* v_fallback_1348_, lean_object* v_x_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1347_, v_fallback_1348_, v_x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1351_, lean_object* v_a_1352_, lean_object* v_fallback_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(v_00_u03b2_1351_, v_a_1352_, v_fallback_1353_, v_x_1354_);
lean_dec(v_x_1354_);
lean_dec(v_fallback_1353_);
lean_dec(v_a_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object* v_00_u03b1_1356_, lean_object* v_a_1357_, lean_object* v_n_1358_, lean_object* v_lo_1359_, lean_object* v_hi_1360_, lean_object* v_hhi_1361_, lean_object* v_pivot_1362_, lean_object* v_as_1363_, lean_object* v_i_1364_, lean_object* v_k_1365_, lean_object* v_ilo_1366_, lean_object* v_ik_1367_, lean_object* v_w_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1357_, v_hi_1360_, v_pivot_1362_, v_as_1363_, v_i_1364_, v_k_1365_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_a_1371_, lean_object* v_n_1372_, lean_object* v_lo_1373_, lean_object* v_hi_1374_, lean_object* v_hhi_1375_, lean_object* v_pivot_1376_, lean_object* v_as_1377_, lean_object* v_i_1378_, lean_object* v_k_1379_, lean_object* v_ilo_1380_, lean_object* v_ik_1381_, lean_object* v_w_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(v_00_u03b1_1370_, v_a_1371_, v_n_1372_, v_lo_1373_, v_hi_1374_, v_hhi_1375_, v_pivot_1376_, v_as_1377_, v_i_1378_, v_k_1379_, v_ilo_1380_, v_ik_1381_, v_w_1382_);
lean_dec_ref(v_pivot_1376_);
lean_dec(v_hi_1374_);
lean_dec(v_lo_1373_);
lean_dec(v_n_1372_);
lean_dec_ref(v_a_1371_);
return v_res_1383_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
lean_ctor_set(v___x_1386_, 2, v___x_1385_);
lean_ctor_set(v___x_1386_, 3, v___x_1385_);
lean_ctor_set(v___x_1386_, 4, v___x_1384_);
lean_ctor_set(v___x_1386_, 5, v___x_1384_);
lean_ctor_set(v___x_1386_, 6, v___x_1384_);
lean_ctor_set(v___x_1386_, 7, v___x_1384_);
lean_ctor_set(v___x_1386_, 8, v___x_1384_);
lean_ctor_set(v___x_1386_, 9, v___x_1384_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_unsigned_to_nat(32u);
v___x_1388_ = lean_mk_empty_array_with_capacity(v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2(void){
_start:
{
size_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1390_ = ((size_t)5ULL);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_unsigned_to_nat(32u);
v___x_1393_ = lean_mk_empty_array_with_capacity(v___x_1392_);
v___x_1394_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1);
v___x_1395_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1393_);
lean_ctor_set(v___x_1395_, 2, v___x_1391_);
lean_ctor_set(v___x_1395_, 3, v___x_1391_);
lean_ctor_set_usize(v___x_1395_, 4, v___x_1390_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(1);
v___x_1397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2);
v___x_1398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v___x_1397_);
lean_ctor_set(v___x_1399_, 2, v___x_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object* v_msgData_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v_options_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1404_ = lean_st_ref_get(v___y_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v_options_1406_ = lean_ctor_get(v___y_1401_, 2);
v___x_1407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1408_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
lean_inc_ref(v_options_1406_);
v___x_1409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1409_, 0, v_env_1405_);
lean_ctor_set(v___x_1409_, 1, v___x_1407_);
lean_ctor_set(v___x_1409_, 2, v___x_1408_);
lean_ctor_set(v___x_1409_, 3, v_options_1406_);
v___x_1410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_msgData_1400_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object* v_msgData_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msgData_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
if (lean_obj_tag(v_a_1417_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = l_List_reverse___redArg(v_a_1418_);
return v___x_1419_;
}
else
{
lean_object* v_head_1420_; lean_object* v_tail_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1430_; 
v_head_1420_ = lean_ctor_get(v_a_1417_, 0);
v_tail_1421_ = lean_ctor_get(v_a_1417_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_a_1417_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1423_ = v_a_1417_;
v_isShared_1424_ = v_isSharedCheck_1430_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_tail_1421_);
lean_inc(v_head_1420_);
lean_dec(v_a_1417_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1430_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = l_Lean_mkLevelParam(v_head_1420_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_a_1418_);
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_a_1418_);
v___x_1427_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v_a_1417_ = v_tail_1421_;
v_a_1418_ = v___x_1427_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_ref_1435_; lean_object* v___x_1436_; lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_ref_1435_ = lean_ctor_get(v___y_1432_, 5);
v___x_1436_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msg_1431_, v___y_1432_, v___y_1433_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_inc(v_ref_1435_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_ref_1435_);
lean_ctor_set(v___x_1441_, 1, v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 1);
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_fileName_1456_; lean_object* v_fileMap_1457_; lean_object* v_options_1458_; lean_object* v_currRecDepth_1459_; lean_object* v_maxRecDepth_1460_; lean_object* v_ref_1461_; lean_object* v_currNamespace_1462_; lean_object* v_openDecls_1463_; lean_object* v_initHeartbeats_1464_; lean_object* v_maxHeartbeats_1465_; lean_object* v_quotContext_1466_; lean_object* v_currMacroScope_1467_; uint8_t v_diag_1468_; lean_object* v_cancelTk_x3f_1469_; uint8_t v_suppressElabErrors_1470_; lean_object* v_inheritedTraceOptions_1471_; lean_object* v_ref_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_fileName_1456_ = lean_ctor_get(v___y_1453_, 0);
v_fileMap_1457_ = lean_ctor_get(v___y_1453_, 1);
v_options_1458_ = lean_ctor_get(v___y_1453_, 2);
v_currRecDepth_1459_ = lean_ctor_get(v___y_1453_, 3);
v_maxRecDepth_1460_ = lean_ctor_get(v___y_1453_, 4);
v_ref_1461_ = lean_ctor_get(v___y_1453_, 5);
v_currNamespace_1462_ = lean_ctor_get(v___y_1453_, 6);
v_openDecls_1463_ = lean_ctor_get(v___y_1453_, 7);
v_initHeartbeats_1464_ = lean_ctor_get(v___y_1453_, 8);
v_maxHeartbeats_1465_ = lean_ctor_get(v___y_1453_, 9);
v_quotContext_1466_ = lean_ctor_get(v___y_1453_, 10);
v_currMacroScope_1467_ = lean_ctor_get(v___y_1453_, 11);
v_diag_1468_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*14);
v_cancelTk_x3f_1469_ = lean_ctor_get(v___y_1453_, 12);
v_suppressElabErrors_1470_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1471_ = lean_ctor_get(v___y_1453_, 13);
v_ref_1472_ = l_Lean_replaceRef(v_ref_1451_, v_ref_1461_);
lean_inc_ref(v_inheritedTraceOptions_1471_);
lean_inc(v_cancelTk_x3f_1469_);
lean_inc(v_currMacroScope_1467_);
lean_inc(v_quotContext_1466_);
lean_inc(v_maxHeartbeats_1465_);
lean_inc(v_initHeartbeats_1464_);
lean_inc(v_openDecls_1463_);
lean_inc(v_currNamespace_1462_);
lean_inc(v_maxRecDepth_1460_);
lean_inc(v_currRecDepth_1459_);
lean_inc_ref(v_options_1458_);
lean_inc_ref(v_fileMap_1457_);
lean_inc_ref(v_fileName_1456_);
v___x_1473_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1473_, 0, v_fileName_1456_);
lean_ctor_set(v___x_1473_, 1, v_fileMap_1457_);
lean_ctor_set(v___x_1473_, 2, v_options_1458_);
lean_ctor_set(v___x_1473_, 3, v_currRecDepth_1459_);
lean_ctor_set(v___x_1473_, 4, v_maxRecDepth_1460_);
lean_ctor_set(v___x_1473_, 5, v_ref_1472_);
lean_ctor_set(v___x_1473_, 6, v_currNamespace_1462_);
lean_ctor_set(v___x_1473_, 7, v_openDecls_1463_);
lean_ctor_set(v___x_1473_, 8, v_initHeartbeats_1464_);
lean_ctor_set(v___x_1473_, 9, v_maxHeartbeats_1465_);
lean_ctor_set(v___x_1473_, 10, v_quotContext_1466_);
lean_ctor_set(v___x_1473_, 11, v_currMacroScope_1467_);
lean_ctor_set(v___x_1473_, 12, v_cancelTk_x3f_1469_);
lean_ctor_set(v___x_1473_, 13, v_inheritedTraceOptions_1471_);
lean_ctor_set_uint8(v___x_1473_, sizeof(void*)*14, v_diag_1468_);
lean_ctor_set_uint8(v___x_1473_, sizeof(void*)*14 + 1, v_suppressElabErrors_1470_);
v___x_1474_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1452_, v___x_1473_, v___y_1454_);
lean_dec_ref(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1475_, v_msg_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_ref_1475_);
return v_res_1480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1502_, lean_object* v_declHint_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v_env_1507_; uint8_t v___x_1508_; 
v___x_1506_ = lean_st_ref_get(v___y_1504_);
v_env_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc_ref(v_env_1507_);
lean_dec(v___x_1506_);
v___x_1508_ = l_Lean_Name_isAnonymous(v_declHint_1503_);
if (v___x_1508_ == 0)
{
uint8_t v_isExporting_1509_; 
v_isExporting_1509_ = lean_ctor_get_uint8(v_env_1507_, sizeof(void*)*8);
if (v_isExporting_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v_env_1507_);
lean_dec(v_declHint_1503_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_msg_1502_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
lean_inc_ref(v_env_1507_);
v___x_1511_ = l_Lean_Environment_setExporting(v_env_1507_, v___x_1508_);
lean_inc(v_declHint_1503_);
lean_inc_ref(v___x_1511_);
v___x_1512_ = l_Lean_Environment_contains(v___x_1511_, v_declHint_1503_, v_isExporting_1509_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v___x_1511_);
lean_dec_ref(v_env_1507_);
lean_dec(v_declHint_1503_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_msg_1502_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_c_1519_; lean_object* v___x_1520_; 
v___x_1514_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1515_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
v___x_1516_ = l_Lean_Options_empty;
v___x_1517_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1511_);
lean_ctor_set(v___x_1517_, 1, v___x_1514_);
lean_ctor_set(v___x_1517_, 2, v___x_1515_);
lean_ctor_set(v___x_1517_, 3, v___x_1516_);
lean_inc(v_declHint_1503_);
v___x_1518_ = l_Lean_MessageData_ofConstName(v_declHint_1503_, v___x_1508_);
v_c_1519_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1519_, 0, v___x_1517_);
lean_ctor_set(v_c_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1507_, v_declHint_1503_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref(v_env_1507_);
lean_dec(v_declHint_1503_);
v___x_1521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v_c_1519_);
v___x_1523_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_MessageData_note(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_msg_1502_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1563_; 
v_val_1528_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1530_ = v___x_1520_;
v_isShared_1531_ = v_isSharedCheck_1563_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v___x_1520_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1563_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_mod_1535_; uint8_t v___x_1536_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Lean_Environment_header(v_env_1507_);
lean_dec_ref(v_env_1507_);
v___x_1534_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1533_);
v_mod_1535_ = lean_array_get(v___x_1532_, v___x_1534_, v_val_1528_);
lean_dec(v_val_1528_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = l_Lean_isPrivateName(v_declHint_1503_);
lean_dec(v_declHint_1503_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v_c_1519_);
v___x_1539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_MessageData_ofName(v_mod_1535_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_MessageData_note(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_msg_1502_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1546_);
v___x_1548_ = v___x_1530_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_c_1519_);
v___x_1552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_MessageData_ofName(v_mod_1535_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_MessageData_note(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_msg_1502_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1559_);
v___x_1561_ = v___x_1530_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1564_; 
lean_dec_ref(v_env_1507_);
lean_dec(v_declHint_1503_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_msg_1502_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1565_, lean_object* v_declHint_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1565_, v_declHint_1566_, v___y_1567_);
lean_dec(v___y_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_1570_, lean_object* v_declHint_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
v___x_1575_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1570_, v_declHint_1571_, v___y_1573_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = l_Lean_unknownIdentifierMessageTag;
v___x_1581_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_1586_, lean_object* v_declHint_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1586_, v_declHint_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1592_, lean_object* v_msg_1593_, lean_object* v_declHint_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___x_1600_; 
v___x_1598_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1593_, v_declHint_1594_, v___y_1595_, v___y_1596_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1592_, v_a_1599_, v___y_1595_, v___y_1596_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1601_, lean_object* v_msg_1602_, lean_object* v_declHint_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1601_, v_msg_1602_, v_declHint_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v_ref_1601_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1614_, lean_object* v_constName_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1619_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1620_ = 0;
lean_inc(v_constName_1615_);
v___x_1621_ = l_Lean_MessageData_ofConstName(v_constName_1615_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1614_, v___x_1624_, v_constName_1615_, v___y_1616_, v___y_1617_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1626_, lean_object* v_constName_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1626_, v_constName_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v_ref_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_ref_1636_; lean_object* v___x_1637_; 
v_ref_1636_ = lean_ctor_get(v___y_1633_, 5);
v___x_1637_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1636_, v_constName_1632_, v___y_1633_, v___y_1634_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object* v_constName_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v_env_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = lean_st_ref_get(v___y_1645_);
v_env_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc_ref(v_env_1648_);
lean_dec(v___x_1647_);
v___x_1649_ = 0;
lean_inc(v_constName_1643_);
v___x_1650_ = l_Lean_Environment_findConstVal_x3f(v_env_1648_, v_constName_1643_, v___x_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1643_, v___y_1644_, v___y_1645_);
return v___x_1651_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_constName_1643_);
v_val_1652_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1650_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_val_1652_);
lean_dec(v___x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set_tag(v___x_1654_, 0);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_val_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object* v_constName_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object* v_constName_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
lean_inc(v_constName_1665_);
v___x_1669_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1681_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1681_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1681_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_levelParams_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v_levelParams_1674_ = lean_ctor_get(v_a_1670_, 1);
lean_inc(v_levelParams_1674_);
lean_dec(v_a_1670_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(v_levelParams_1674_, v___x_1675_);
v___x_1677_ = l_Lean_mkConst(v_constName_1665_, v___x_1676_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1677_);
v___x_1679_ = v___x_1672_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_constName_1665_);
v_a_1682_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1669_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1669_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object* v_constName_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_constName_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1694_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__1(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__0));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__3(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__2));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__5(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__4));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__7(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__6));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__9(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__8));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__11(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__10));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object* v_declName_1713_, lean_object* v_warning_1714_, uint8_t v_useErrorFormat_1715_, lean_object* v_filePath_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___y_1721_; lean_object* v___y_1722_; 
if (v_useErrorFormat_1715_ == 0)
{
lean_dec_ref(v_filePath_1716_);
v___y_1721_ = v_a_1717_;
v___y_1722_ = v_a_1718_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1742_; 
lean_inc(v_declName_1713_);
v___x_1742_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1713_, v_a_1717_, v_a_1718_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1742_);
if (lean_obj_tag(v_a_1743_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1800_; 
v_val_1744_ = lean_ctor_get(v_a_1743_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1746_ = v_a_1743_;
v_isShared_1747_ = v_isSharedCheck_1800_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_val_1744_);
lean_dec(v_a_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1800_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1713_, v_a_1717_, v_a_1718_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_range_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1790_; 
v_range_1749_ = lean_ctor_get(v_val_1744_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_val_1744_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_val_1744_, 1);
lean_dec(v_unused_1791_);
v___x_1751_ = v_val_1744_;
v_isShared_1752_ = v_isSharedCheck_1790_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_range_1749_);
lean_dec(v_val_1744_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1790_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_pos_1753_; lean_object* v_a_1754_; lean_object* v_line_1755_; lean_object* v_column_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1789_; 
v_pos_1753_ = lean_ctor_get(v_range_1749_, 0);
lean_inc_ref(v_pos_1753_);
lean_dec_ref(v_range_1749_);
v_a_1754_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1748_);
v_line_1755_ = lean_ctor_get(v_pos_1753_, 0);
v_column_1756_ = lean_ctor_get(v_pos_1753_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_pos_1753_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1758_ = v_pos_1753_;
v_isShared_1759_ = v_isSharedCheck_1789_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_column_1756_);
lean_inc(v_line_1755_);
lean_dec(v_pos_1753_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1789_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 3);
lean_ctor_set(v___x_1746_, 0, v_filePath_1716_);
v___x_1761_ = v___x_1746_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_filePath_1716_);
v___x_1761_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = l_Lean_MessageData_ofFormat(v___x_1761_);
v___x_1763_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__7, &l_Lean_Linter_EnvLinter_printWarning___closed__7_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__7);
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 7);
lean_ctor_set(v___x_1758_, 1, v___x_1763_);
lean_ctor_set(v___x_1758_, 0, v___x_1762_);
v___x_1765_ = v___x_1758_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1766_ = l_Nat_reprFast(v_line_1755_);
v___x_1767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
v___x_1768_ = l_Lean_MessageData_ofFormat(v___x_1767_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 7);
lean_ctor_set(v___x_1751_, 1, v___x_1768_);
lean_ctor_set(v___x_1751_, 0, v___x_1765_);
v___x_1770_ = v___x_1751_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1763_);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_add(v_column_1756_, v___x_1772_);
lean_dec(v_column_1756_);
v___x_1774_ = l_Nat_reprFast(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
v___x_1776_ = l_Lean_MessageData_ofFormat(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1771_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__9, &l_Lean_Linter_EnvLinter_printWarning___closed__9_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__9);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_MessageData_ofExpr(v_a_1754_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__11, &l_Lean_Linter_EnvLinter_printWarning___closed__11_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__11);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_warning_1714_);
v___x_1785_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1784_, v_a_1717_, v_a_1718_);
return v___x_1785_;
}
}
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_del_object(v___x_1746_);
lean_dec(v_val_1744_);
lean_dec_ref(v_filePath_1716_);
lean_dec_ref(v_warning_1714_);
v_a_1792_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1748_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1748_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
else
{
lean_dec(v_a_1743_);
lean_dec_ref(v_filePath_1716_);
v___y_1721_ = v_a_1717_;
v___y_1722_ = v_a_1718_;
goto v___jp_1720_;
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_filePath_1716_);
lean_dec_ref(v_warning_1714_);
lean_dec(v_declName_1713_);
v_a_1801_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1742_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1742_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
v___jp_1720_:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1713_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__1, &l_Lean_Linter_EnvLinter_printWarning___closed__1_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__1);
v___x_1726_ = l_Lean_MessageData_ofExpr(v_a_1724_);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__3, &l_Lean_Linter_EnvLinter_printWarning___closed__3_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__3);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_warning_1714_);
v___x_1731_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1732_, v___y_1721_, v___y_1722_);
return v___x_1733_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec_ref(v_warning_1714_);
v_a_1734_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1723_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1723_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object* v_declName_1809_, lean_object* v_warning_1810_, lean_object* v_useErrorFormat_1811_, lean_object* v_filePath_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
uint8_t v_useErrorFormat_boxed_1816_; lean_object* v_res_1817_; 
v_useErrorFormat_boxed_1816_ = lean_unbox(v_useErrorFormat_1811_);
v_res_1817_ = l_Lean_Linter_EnvLinter_printWarning(v_declName_1809_, v_warning_1810_, v_useErrorFormat_boxed_1816_, v_filePath_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1818_, lean_object* v_constName_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1819_, v___y_1820_, v___y_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_constName_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(v_00_u03b1_1824_, v_constName_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1830_, lean_object* v_ref_1831_, lean_object* v_constName_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1831_, v_constName_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_ref_1838_, lean_object* v_constName_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1837_, v_ref_1838_, v_constName_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v_ref_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1844_, lean_object* v_ref_1845_, lean_object* v_msg_1846_, lean_object* v_declHint_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1845_, v_msg_1846_, v_declHint_1847_, v___y_1848_, v___y_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_ref_1853_, lean_object* v_msg_1854_, lean_object* v_declHint_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1852_, v_ref_1853_, v_msg_1854_, v_declHint_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v_ref_1853_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_1860_, lean_object* v_declHint_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1860_, v_declHint_1861_, v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_1866_, lean_object* v_declHint_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_1866_, v_declHint_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1872_, lean_object* v_ref_1873_, lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1873_, v_msg_1874_, v___y_1875_, v___y_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1879_, lean_object* v_ref_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1879_, v_ref_1880_, v_msg_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_ref_1880_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_1886_, lean_object* v_msg_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_msg_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_1892_, v_msg_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t v_useErrorFormat_1898_, lean_object* v_filePath_1899_, size_t v_sz_1900_, size_t v_i_1901_, lean_object* v_bs_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_lt(v_i_1901_, v_sz_1900_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_dec_ref(v_filePath_1899_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_bs_1902_);
return v___x_1907_;
}
else
{
lean_object* v_v_1908_; lean_object* v_fst_1909_; lean_object* v_snd_1910_; lean_object* v___x_1911_; 
v_v_1908_ = lean_array_uget_borrowed(v_bs_1902_, v_i_1901_);
v_fst_1909_ = lean_ctor_get(v_v_1908_, 0);
v_snd_1910_ = lean_ctor_get(v_v_1908_, 1);
lean_inc_ref(v_filePath_1899_);
lean_inc(v_snd_1910_);
lean_inc(v_fst_1909_);
v___x_1911_ = l_Lean_Linter_EnvLinter_printWarning(v_fst_1909_, v_snd_1910_, v_useErrorFormat_1898_, v_filePath_1899_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v_bs_x27_1914_; size_t v___x_1915_; size_t v___x_1916_; lean_object* v___x_1917_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = lean_unsigned_to_nat(0u);
v_bs_x27_1914_ = lean_array_uset(v_bs_1902_, v_i_1901_, v___x_1913_);
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1901_, v___x_1915_);
v___x_1917_ = lean_array_uset(v_bs_x27_1914_, v_i_1901_, v_a_1912_);
v_i_1901_ = v___x_1916_;
v_bs_1902_ = v___x_1917_;
goto _start;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_bs_1902_);
lean_dec_ref(v_filePath_1899_);
v_a_1919_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1911_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1911_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object* v_useErrorFormat_1927_, lean_object* v_filePath_1928_, lean_object* v_sz_1929_, lean_object* v_i_1930_, lean_object* v_bs_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v_useErrorFormat_boxed_1935_; size_t v_sz_boxed_1936_; size_t v_i_boxed_1937_; lean_object* v_res_1938_; 
v_useErrorFormat_boxed_1935_ = lean_unbox(v_useErrorFormat_1927_);
v_sz_boxed_1936_ = lean_unbox_usize(v_sz_1929_);
lean_dec(v_sz_1929_);
v_i_boxed_1937_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_res_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_boxed_1935_, v_filePath_1928_, v_sz_boxed_1936_, v_i_boxed_1937_, v_bs_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1938_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_box(1);
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object* v_results_1941_, lean_object* v_filePath_1942_, uint8_t v_useErrorFormat_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1941_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v_sz_1949_ = lean_array_size(v_a_1948_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_1943_, v_filePath_1942_, v_sz_1949_, v___x_1950_, v_a_1948_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1962_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1956_ = lean_array_to_list(v_a_1952_);
v___x_1957_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_1958_ = l_Lean_MessageData_joinSep(v___x_1956_, v___x_1957_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1958_);
v___x_1960_ = v___x_1954_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v_a_1963_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1951_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1951_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v_filePath_1942_);
v_a_1971_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1947_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1947_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object* v_results_1979_, lean_object* v_filePath_1980_, lean_object* v_useErrorFormat_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v_useErrorFormat_boxed_1985_; lean_object* v_res_1986_; 
v_useErrorFormat_boxed_1985_ = lean_unbox(v_useErrorFormat_1981_);
v_res_1986_ = l_Lean_Linter_EnvLinter_printWarnings(v_results_1979_, v_filePath_1980_, v_useErrorFormat_boxed_1985_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec_ref(v_results_1979_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 0)
{
return v_x_1987_;
}
else
{
lean_object* v_key_1989_; lean_object* v_value_1990_; lean_object* v_tail_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_key_1989_ = lean_ctor_get(v_x_1988_, 0);
v_value_1990_ = lean_ctor_get(v_x_1988_, 1);
v_tail_1991_ = lean_ctor_get(v_x_1988_, 2);
lean_inc(v_value_1990_);
lean_inc(v_key_1989_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_key_1989_);
lean_ctor_set(v___x_1992_, 1, v_value_1990_);
v___x_1993_ = lean_array_push(v_x_1987_, v___x_1992_);
v_x_1987_ = v___x_1993_;
v_x_1988_ = v_tail_1991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_x_1995_, v_x_1996_);
lean_dec(v_x_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object* v_as_1998_, size_t v_i_1999_, size_t v_stop_2000_, lean_object* v_b_2001_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_eq(v_i_1999_, v_stop_2000_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; size_t v___x_2005_; size_t v___x_2006_; 
v___x_2003_ = lean_array_uget_borrowed(v_as_1998_, v_i_1999_);
v___x_2004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_b_2001_, v___x_2003_);
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_add(v_i_1999_, v___x_2005_);
v_i_1999_ = v___x_2006_;
v_b_2001_ = v___x_2004_;
goto _start;
}
else
{
return v_b_2001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_stop_2010_, lean_object* v_b_2011_){
_start:
{
size_t v_i_boxed_2012_; size_t v_stop_boxed_2013_; lean_object* v_res_2014_; 
v_i_boxed_2012_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_stop_boxed_2013_ = lean_unbox_usize(v_stop_2010_);
lean_dec(v_stop_2010_);
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_as_2008_, v_i_boxed_2012_, v_stop_boxed_2013_, v_b_2011_);
lean_dec_ref(v_as_2008_);
return v_res_2014_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0));
v___x_2017_ = l_Lean_stringToMessageData(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t v_useErrorFormat_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = l_List_reverse___redArg(v_x_2023_);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v_head_2029_; lean_object* v_tail_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2073_; 
v_head_2029_ = lean_ctor_get(v_x_2022_, 0);
v_tail_2030_ = lean_ctor_get(v_x_2022_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_x_2022_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2032_ = v_x_2022_;
v_isShared_2033_ = v_isSharedCheck_2073_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_tail_2030_);
lean_inc(v_head_2029_);
lean_dec(v_x_2022_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2073_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_a_2035_; lean_object* v_snd_2040_; lean_object* v_fst_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2072_; 
v_snd_2040_ = lean_ctor_get(v_head_2029_, 1);
v_fst_2041_ = lean_ctor_get(v_head_2029_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_head_2029_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2043_ = v_head_2029_;
v_isShared_2044_ = v_isSharedCheck_2072_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_snd_2040_);
lean_inc(v_fst_2041_);
lean_dec(v_head_2029_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2072_;
goto v_resetjp_2042_;
}
v___jp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_x_2023_);
lean_ctor_set(v___x_2032_, 0, v_a_2035_);
v___x_2037_ = v___x_2032_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2035_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_x_2023_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v_x_2022_ = v_tail_2030_;
v_x_2023_ = v___x_2037_;
goto _start;
}
}
v_resetjp_2042_:
{
lean_object* v_fst_2045_; lean_object* v_snd_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2071_; 
v_fst_2045_ = lean_ctor_get(v_snd_2040_, 0);
v_snd_2046_ = lean_ctor_get(v_snd_2040_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_snd_2040_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2048_ = v_snd_2040_;
v_isShared_2049_ = v_isSharedCheck_2071_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_snd_2046_);
lean_inc(v_fst_2045_);
lean_dec(v_snd_2040_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2071_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2046_, v_fst_2045_, v_useErrorFormat_2021_, v___y_2024_, v___y_2025_);
lean_dec(v_snd_2046_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1);
v___x_2053_ = l_Lean_MessageData_ofName(v_fst_2041_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 7);
lean_ctor_set(v___x_2048_, 1, v___x_2053_);
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2055_ = v___x_2048_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 7);
lean_ctor_set(v___x_2043_, 1, v___x_2056_);
lean_ctor_set(v___x_2043_, 0, v___x_2055_);
v___x_2058_ = v___x_2043_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_a_2051_);
v_a_2035_ = v___x_2059_;
goto v___jp_2034_;
}
}
}
else
{
lean_del_object(v___x_2048_);
lean_del_object(v___x_2043_);
lean_dec(v_fst_2041_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2050_);
v_a_2035_ = v_a_2062_;
goto v___jp_2034_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_del_object(v___x_2032_);
lean_dec(v_tail_2030_);
lean_dec(v_x_2023_);
v_a_2063_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2050_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2050_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object* v_useErrorFormat_2074_, lean_object* v_x_2075_, lean_object* v_x_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
uint8_t v_useErrorFormat_boxed_2080_; lean_object* v_res_2081_; 
v_useErrorFormat_boxed_2080_ = lean_unbox(v_useErrorFormat_2074_);
v_res_2081_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_boxed_2080_, v_x_2075_, v_x_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object* v_a_2082_, lean_object* v_x_2083_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_box(0);
return v___x_2084_;
}
else
{
lean_object* v_key_2085_; lean_object* v_value_2086_; lean_object* v_tail_2087_; uint8_t v___x_2088_; 
v_key_2085_ = lean_ctor_get(v_x_2083_, 0);
v_value_2086_ = lean_ctor_get(v_x_2083_, 1);
v_tail_2087_ = lean_ctor_get(v_x_2083_, 2);
v___x_2088_ = lean_name_eq(v_key_2085_, v_a_2082_);
if (v___x_2088_ == 0)
{
v_x_2083_ = v_tail_2087_;
goto _start;
}
else
{
lean_object* v___x_2090_; 
lean_inc(v_value_2086_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_value_2086_);
return v___x_2090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object* v_a_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2091_, v_x_2092_);
lean_dec(v_x_2092_);
lean_dec(v_a_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object* v_m_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_buckets_2096_; lean_object* v___x_2097_; uint64_t v___y_2099_; 
v_buckets_2096_ = lean_ctor_get(v_m_2094_, 1);
v___x_2097_ = lean_array_get_size(v_buckets_2096_);
if (lean_obj_tag(v_a_2095_) == 0)
{
uint64_t v___x_2113_; 
v___x_2113_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_2099_ = v___x_2113_;
goto v___jp_2098_;
}
else
{
uint64_t v_hash_2114_; 
v_hash_2114_ = lean_ctor_get_uint64(v_a_2095_, sizeof(void*)*2);
v___y_2099_ = v_hash_2114_;
goto v___jp_2098_;
}
v___jp_2098_:
{
uint64_t v___x_2100_; uint64_t v___x_2101_; uint64_t v_fold_2102_; uint64_t v___x_2103_; uint64_t v___x_2104_; uint64_t v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2100_ = 32ULL;
v___x_2101_ = lean_uint64_shift_right(v___y_2099_, v___x_2100_);
v_fold_2102_ = lean_uint64_xor(v___y_2099_, v___x_2101_);
v___x_2103_ = 16ULL;
v___x_2104_ = lean_uint64_shift_right(v_fold_2102_, v___x_2103_);
v___x_2105_ = lean_uint64_xor(v_fold_2102_, v___x_2104_);
v___x_2106_ = lean_uint64_to_usize(v___x_2105_);
v___x_2107_ = lean_usize_of_nat(v___x_2097_);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_sub(v___x_2107_, v___x_2108_);
v___x_2110_ = lean_usize_land(v___x_2106_, v___x_2109_);
v___x_2111_ = lean_array_uget_borrowed(v_buckets_2096_, v___x_2110_);
v___x_2112_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2095_, v___x_2111_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object* v_m_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_m_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object* v_key_2118_, lean_object* v_value_2119_, lean_object* v_fp_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_2125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v___x_2124_, v_key_2118_, v_value_2119_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_fp_2120_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object* v_key_2128_, lean_object* v_value_2129_, lean_object* v_fp_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2128_, v_value_2129_, v_fp_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object* v_constName_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v_env_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_st_ref_get(v___y_2137_);
v_env_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc_ref(v_env_2140_);
lean_dec(v___x_2139_);
v___x_2141_ = 0;
lean_inc(v_constName_2135_);
v___x_2142_ = l_Lean_Environment_find_x3f(v_env_2140_, v_constName_2135_, v___x_2141_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_2135_, v___y_2136_, v___y_2137_);
return v___x_2143_;
}
else
{
lean_object* v_val_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_constName_2135_);
v_val_2144_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2142_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_val_2144_);
lean_dec(v___x_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 0);
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_val_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object* v_constName_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_constName_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object* v_declName_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; 
lean_inc(v_declName_2157_);
v___x_2161_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_declName_2157_, v___y_2158_, v___y_2159_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2188_; 
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2161_, 0);
lean_dec(v_unused_2189_);
v___x_2163_ = v___x_2161_;
v_isShared_2164_ = v_isSharedCheck_2188_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v___x_2161_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2188_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v_env_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_st_ref_get(v___y_2159_);
v_env_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_ref(v_env_2166_);
lean_dec(v___x_2165_);
v___x_2167_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2166_, v_declName_2157_);
lean_dec(v_declName_2157_);
lean_dec_ref(v_env_2166_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_box(0);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2168_);
v___x_2170_ = v___x_2163_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
else
{
lean_object* v_val_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2187_; 
v_val_2172_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2174_ = v___x_2167_;
v_isShared_2175_ = v_isSharedCheck_2187_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_val_2172_);
lean_dec(v___x_2167_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2187_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2176_ = lean_st_ref_get(v___y_2159_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_ref(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2178_ = lean_box(0);
v___x_2179_ = l_Lean_Environment_allImportedModuleNames(v_env_2177_);
lean_dec_ref(v_env_2177_);
v___x_2180_ = lean_array_get(v___x_2178_, v___x_2179_, v_val_2172_);
lean_dec(v_val_2172_);
lean_dec_ref(v___x_2179_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2180_);
v___x_2182_ = v___x_2174_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2182_);
v___x_2184_ = v___x_2163_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_declName_2157_);
v_a_2190_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2161_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2161_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object* v_declName_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_declName_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t v_useErrorFormat_2206_, lean_object* v_sp_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
if (lean_obj_tag(v_x_2209_) == 0)
{
lean_object* v___x_2213_; 
lean_dec(v_sp_2207_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_x_2208_);
return v___x_2213_;
}
else
{
lean_object* v_key_2214_; lean_object* v_value_2215_; lean_object* v_tail_2216_; lean_object* v___y_2218_; lean_object* v_a_2219_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___x_2226_; 
v_key_2214_ = lean_ctor_get(v_x_2209_, 0);
lean_inc_n(v_key_2214_, 2);
v_value_2215_ = lean_ctor_get(v_x_2209_, 1);
lean_inc(v_value_2215_);
v_tail_2216_ = lean_ctor_get(v_x_2209_, 2);
lean_inc(v_tail_2216_);
lean_dec_ref(v_x_2209_);
v___x_2226_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_key_2214_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; lean_object* v___y_2230_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref(v___x_2226_);
v___x_2228_ = lean_st_ref_get(v___y_2211_);
if (lean_obj_tag(v_a_2227_) == 0)
{
lean_object* v_env_2266_; lean_object* v___x_2267_; 
v_env_2266_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_env_2266_);
lean_dec(v___x_2228_);
v___x_2267_ = l_Lean_Environment_mainModule(v_env_2266_);
lean_dec_ref(v_env_2266_);
v___y_2230_ = v___x_2267_;
goto v___jp_2229_;
}
else
{
lean_object* v_val_2268_; 
lean_dec(v___x_2228_);
v_val_2268_ = lean_ctor_get(v_a_2227_, 0);
lean_inc(v_val_2268_);
lean_dec_ref(v_a_2227_);
v___y_2230_ = v_val_2268_;
goto v___jp_2229_;
}
v___jp_2229_:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_x_2208_, v___y_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
if (v_useErrorFormat_2206_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2233_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2214_, v_value_2215_, v___x_2232_, v___y_2210_, v___y_2211_);
v___y_2223_ = v___y_2230_;
v___y_2224_ = v___x_2233_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1));
lean_inc(v___y_2230_);
lean_inc(v_sp_2207_);
v___x_2235_ = l_Lean_SearchPath_findWithExt(v_sp_2207_, v___x_2234_, v___y_2230_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2));
lean_inc(v___y_2230_);
v___x_2238_ = l_Lean_modToFilePath(v___x_2237_, v___y_2230_, v___x_2234_);
v___x_2239_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2214_, v_value_2215_, v___x_2238_, v___y_2210_, v___y_2211_);
v___y_2223_ = v___y_2230_;
v___y_2224_ = v___x_2239_;
goto v___jp_2222_;
}
else
{
lean_object* v_val_2240_; lean_object* v___x_2241_; 
v_val_2240_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2240_);
lean_dec_ref(v_a_2236_);
v___x_2241_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2214_, v_value_2215_, v_val_2240_, v___y_2210_, v___y_2211_);
v___y_2223_ = v___y_2230_;
v___y_2224_ = v___x_2241_;
goto v___jp_2222_;
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v___y_2230_);
lean_dec(v_tail_2216_);
lean_dec(v_value_2215_);
lean_dec(v_key_2214_);
lean_dec_ref(v_x_2208_);
lean_dec(v_sp_2207_);
v_a_2242_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2244_ = v___x_2235_;
v_isShared_2245_ = v_isSharedCheck_2254_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2235_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2254_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v_ref_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v_ref_2246_ = lean_ctor_get(v___y_2210_, 5);
v___x_2247_ = lean_io_error_to_string(v_a_2242_);
v___x_2248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
v___x_2249_ = l_Lean_MessageData_ofFormat(v___x_2248_);
lean_inc(v_ref_2246_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_ref_2246_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2250_);
v___x_2252_ = v___x_2244_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_object* v_val_2255_; lean_object* v_fst_2256_; lean_object* v_snd_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2265_; 
v_val_2255_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_val_2255_);
lean_dec_ref(v___x_2231_);
v_fst_2256_ = lean_ctor_get(v_val_2255_, 0);
v_snd_2257_ = lean_ctor_get(v_val_2255_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_val_2255_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2259_ = v_val_2255_;
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_snd_2257_);
lean_inc(v_fst_2256_);
lean_dec(v_val_2255_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_snd_2257_, v_key_2214_, v_value_2215_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2261_);
v___x_2263_ = v___x_2259_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_fst_2256_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
v___y_2218_ = v___y_2230_;
v_a_2219_ = v___x_2263_;
goto v___jp_2217_;
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_tail_2216_);
lean_dec(v_value_2215_);
lean_dec(v_key_2214_);
lean_dec_ref(v_x_2208_);
lean_dec(v_sp_2207_);
v_a_2269_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2226_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2226_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
v___jp_2217_:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_x_2208_, v___y_2218_, v_a_2219_);
v_x_2208_ = v___x_2220_;
v_x_2209_ = v_tail_2216_;
goto _start;
}
v___jp_2222_:
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___y_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___y_2224_);
v___y_2218_ = v___y_2223_;
v_a_2219_ = v_a_2225_;
goto v___jp_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object* v_useErrorFormat_2277_, lean_object* v_sp_2278_, lean_object* v_x_2279_, lean_object* v_x_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_useErrorFormat_boxed_2284_; lean_object* v_res_2285_; 
v_useErrorFormat_boxed_2284_ = lean_unbox(v_useErrorFormat_2277_);
v_res_2285_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_boxed_2284_, v_sp_2278_, v_x_2279_, v_x_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t v_useErrorFormat_2286_, lean_object* v_sp_2287_, lean_object* v_as_2288_, size_t v_i_2289_, size_t v_stop_2290_, lean_object* v_b_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_usize_dec_eq(v_i_2289_, v_stop_2290_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_array_uget_borrowed(v_as_2288_, v_i_2289_);
lean_inc(v___x_2296_);
lean_inc(v_sp_2287_);
v___x_2297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_2286_, v_sp_2287_, v_b_2291_, v___x_2296_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; size_t v___x_2299_; size_t v___x_2300_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = ((size_t)1ULL);
v___x_2300_ = lean_usize_add(v_i_2289_, v___x_2299_);
v_i_2289_ = v___x_2300_;
v_b_2291_ = v_a_2298_;
goto _start;
}
else
{
lean_dec(v_sp_2287_);
return v___x_2297_;
}
}
else
{
lean_object* v___x_2302_; 
lean_dec(v_sp_2287_);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_b_2291_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object* v_useErrorFormat_2303_, lean_object* v_sp_2304_, lean_object* v_as_2305_, lean_object* v_i_2306_, lean_object* v_stop_2307_, lean_object* v_b_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v_useErrorFormat_boxed_2312_; size_t v_i_boxed_2313_; size_t v_stop_boxed_2314_; lean_object* v_res_2315_; 
v_useErrorFormat_boxed_2312_ = lean_unbox(v_useErrorFormat_2303_);
v_i_boxed_2313_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_stop_boxed_2314_ = lean_unbox_usize(v_stop_2307_);
lean_dec(v_stop_2307_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_boxed_2312_, v_sp_2304_, v_as_2305_, v_i_boxed_2313_, v_stop_boxed_2314_, v_b_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_as_2305_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object* v_hi_2316_, lean_object* v_pivot_2317_, lean_object* v_as_2318_, lean_object* v_i_2319_, lean_object* v_k_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = lean_nat_dec_lt(v_k_2320_, v_hi_2316_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_k_2320_);
lean_dec_ref(v_pivot_2317_);
v___x_2322_ = lean_array_fswap(v_as_2318_, v_i_2319_, v_hi_2316_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_i_2319_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
return v___x_2323_;
}
else
{
lean_object* v___x_2324_; lean_object* v_fst_2325_; lean_object* v_fst_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2324_ = lean_array_fget_borrowed(v_as_2318_, v_k_2320_);
v_fst_2325_ = lean_ctor_get(v___x_2324_, 0);
v_fst_2326_ = lean_ctor_get(v_pivot_2317_, 0);
lean_inc(v_fst_2325_);
v___x_2327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2325_, v___x_2321_);
lean_inc(v_fst_2326_);
v___x_2328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2326_, v___x_2321_);
v___x_2329_ = lean_string_dec_lt(v___x_2327_, v___x_2328_);
lean_dec_ref(v___x_2328_);
lean_dec_ref(v___x_2327_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_k_2320_, v___x_2330_);
lean_dec(v_k_2320_);
v_k_2320_ = v___x_2331_;
goto _start;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2333_ = lean_array_fswap(v_as_2318_, v_i_2319_, v_k_2320_);
v___x_2334_ = lean_unsigned_to_nat(1u);
v___x_2335_ = lean_nat_add(v_i_2319_, v___x_2334_);
lean_dec(v_i_2319_);
v___x_2336_ = lean_nat_add(v_k_2320_, v___x_2334_);
lean_dec(v_k_2320_);
v_as_2318_ = v___x_2333_;
v_i_2319_ = v___x_2335_;
v_k_2320_ = v___x_2336_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object* v_hi_2338_, lean_object* v_pivot_2339_, lean_object* v_as_2340_, lean_object* v_i_2341_, lean_object* v_k_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2338_, v_pivot_2339_, v_as_2340_, v_i_2341_, v_k_2342_);
lean_dec(v_hi_2338_);
return v_res_2343_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t v___x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
lean_object* v_fst_2347_; lean_object* v_fst_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_fst_2347_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_fst_2347_);
lean_dec_ref(v_x_2345_);
v_fst_2348_ = lean_ctor_get(v_x_2346_, 0);
lean_inc(v_fst_2348_);
lean_dec_ref(v_x_2346_);
v___x_2349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2347_, v___x_2344_);
v___x_2350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2348_, v___x_2344_);
v___x_2351_ = lean_string_dec_lt(v___x_2349_, v___x_2350_);
lean_dec_ref(v___x_2350_);
lean_dec_ref(v___x_2349_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object* v___x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
uint8_t v___x_5444__boxed_2355_; uint8_t v_res_2356_; lean_object* v_r_2357_; 
v___x_5444__boxed_2355_ = lean_unbox(v___x_2352_);
v_res_2356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_5444__boxed_2355_, v_x_2353_, v_x_2354_);
v_r_2357_ = lean_box(v_res_2356_);
return v_r_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object* v_n_2358_, lean_object* v_as_2359_, lean_object* v_lo_2360_, lean_object* v_hi_2361_){
_start:
{
lean_object* v___y_2363_; uint8_t v___x_2373_; 
v___x_2373_ = lean_nat_dec_lt(v_lo_2360_, v_hi_2361_);
if (v___x_2373_ == 0)
{
lean_dec(v_lo_2360_);
return v_as_2359_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_mid_2376_; lean_object* v___y_2378_; lean_object* v___y_2384_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2374_ = lean_nat_add(v_lo_2360_, v_hi_2361_);
v___x_2375_ = lean_unsigned_to_nat(1u);
v_mid_2376_ = lean_nat_shiftr(v___x_2374_, v___x_2375_);
lean_dec(v___x_2374_);
v___x_2389_ = lean_array_fget_borrowed(v_as_2359_, v_mid_2376_);
v___x_2390_ = lean_array_fget_borrowed(v_as_2359_, v_lo_2360_);
lean_inc(v___x_2390_);
lean_inc(v___x_2389_);
v___x_2391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2373_, v___x_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
v___y_2384_ = v_as_2359_;
goto v___jp_2383_;
}
else
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_array_fswap(v_as_2359_, v_lo_2360_, v_mid_2376_);
v___y_2384_ = v___x_2392_;
goto v___jp_2383_;
}
v___jp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2379_ = lean_array_fget_borrowed(v___y_2378_, v_mid_2376_);
v___x_2380_ = lean_array_fget_borrowed(v___y_2378_, v_hi_2361_);
lean_inc(v___x_2380_);
lean_inc(v___x_2379_);
v___x_2381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2373_, v___x_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_dec(v_mid_2376_);
v___y_2363_ = v___y_2378_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_array_fswap(v___y_2378_, v_mid_2376_, v_hi_2361_);
lean_dec(v_mid_2376_);
v___y_2363_ = v___x_2382_;
goto v___jp_2362_;
}
}
v___jp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2385_ = lean_array_fget_borrowed(v___y_2384_, v_hi_2361_);
v___x_2386_ = lean_array_fget_borrowed(v___y_2384_, v_lo_2360_);
lean_inc(v___x_2386_);
lean_inc(v___x_2385_);
v___x_2387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2373_, v___x_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
v___y_2378_ = v___y_2384_;
goto v___jp_2377_;
}
else
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_array_fswap(v___y_2384_, v_lo_2360_, v_hi_2361_);
v___y_2378_ = v___x_2388_;
goto v___jp_2377_;
}
}
}
v___jp_2362_:
{
lean_object* v_pivot_2364_; lean_object* v___x_2365_; lean_object* v_fst_2366_; lean_object* v_snd_2367_; uint8_t v___x_2368_; 
v_pivot_2364_ = lean_array_fget(v___y_2363_, v_hi_2361_);
lean_inc_n(v_lo_2360_, 2);
v___x_2365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2361_, v_pivot_2364_, v___y_2363_, v_lo_2360_, v_lo_2360_);
v_fst_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_fst_2366_);
v_snd_2367_ = lean_ctor_get(v___x_2365_, 1);
lean_inc(v_snd_2367_);
lean_dec_ref(v___x_2365_);
v___x_2368_ = lean_nat_dec_le(v_hi_2361_, v_fst_2366_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2358_, v_snd_2367_, v_lo_2360_, v_fst_2366_);
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = lean_nat_add(v_fst_2366_, v___x_2370_);
lean_dec(v_fst_2366_);
v_as_2359_ = v___x_2369_;
v_lo_2360_ = v___x_2371_;
goto _start;
}
else
{
lean_dec(v_fst_2366_);
lean_dec(v_lo_2360_);
return v_snd_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object* v_n_2393_, lean_object* v_as_2394_, lean_object* v_lo_2395_, lean_object* v_hi_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2393_, v_as_2394_, v_lo_2395_, v_hi_2396_);
lean_dec(v_hi_2396_);
lean_dec(v_n_2393_);
return v_res_2397_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object* v_results_2400_, uint8_t v_useErrorFormat_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_size_2459_; lean_object* v_buckets_2460_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v_sp_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; 
if (v_useErrorFormat_2401_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_box(0);
v_sp_2488_ = v___x_2504_;
v___y_2489_ = v_a_2402_;
v___y_2490_ = v_a_2403_;
goto v___jp_2487_;
}
else
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v_sp_2488_ = v_a_2506_;
v___y_2489_ = v_a_2402_;
v___y_2490_ = v_a_2403_;
goto v___jp_2487_;
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2519_; 
v_a_2507_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2509_ = v___x_2505_;
v_isShared_2510_ = v_isSharedCheck_2519_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2505_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2519_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_ref_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v_ref_2511_ = lean_ctor_get(v_a_2402_, 5);
v___x_2512_ = lean_io_error_to_string(v_a_2507_);
v___x_2513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
v___x_2514_ = l_Lean_MessageData_ofFormat(v___x_2513_);
lean_inc(v_ref_2511_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_ref_2511_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2515_);
v___x_2517_ = v___x_2509_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
v___jp_2405_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = lean_array_to_list(v___y_2408_);
v___x_2410_ = lean_box(0);
v___x_2411_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_2401_, v___x_2409_, v___x_2410_, v___y_2406_, v___y_2407_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2421_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2421_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2421_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2416_ = lean_obj_once(&l_Lean_Linter_EnvLinter_groupedByFilename___closed__0, &l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once, _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0);
v___x_2417_ = l_Lean_MessageData_joinSep(v_a_2412_, v___x_2416_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2417_);
v___x_2419_ = v___x_2414_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_a_2422_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2411_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2411_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
v___jp_2430_:
{
lean_object* v___x_2437_; 
v___x_2437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v___y_2434_, v___y_2432_, v___y_2433_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec(v___y_2434_);
v___y_2406_ = v___y_2431_;
v___y_2407_ = v___y_2435_;
v___y_2408_ = v___x_2437_;
goto v___jp_2405_;
}
v___jp_2438_:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_nat_dec_le(v___y_2444_, v___y_2441_);
if (v___x_2445_ == 0)
{
lean_dec(v___y_2441_);
lean_inc(v___y_2444_);
v___y_2431_ = v___y_2440_;
v___y_2432_ = v___y_2439_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___y_2442_;
v___y_2435_ = v___y_2443_;
v___y_2436_ = v___y_2444_;
goto v___jp_2430_;
}
else
{
v___y_2431_ = v___y_2440_;
v___y_2432_ = v___y_2439_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___y_2442_;
v___y_2435_ = v___y_2443_;
v___y_2436_ = v___y_2441_;
goto v___jp_2430_;
}
}
v___jp_2446_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2450_ = lean_array_get_size(v___y_2449_);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = lean_nat_dec_eq(v___x_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = lean_nat_sub(v___x_2450_, v___x_2453_);
v___x_2455_ = lean_nat_dec_le(v___x_2451_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_inc(v___x_2454_);
v___y_2439_ = v___y_2449_;
v___y_2440_ = v___y_2447_;
v___y_2441_ = v___x_2454_;
v___y_2442_ = v___x_2450_;
v___y_2443_ = v___y_2448_;
v___y_2444_ = v___x_2454_;
goto v___jp_2438_;
}
else
{
v___y_2439_ = v___y_2449_;
v___y_2440_ = v___y_2447_;
v___y_2441_ = v___x_2454_;
v___y_2442_ = v___x_2450_;
v___y_2443_ = v___y_2448_;
v___y_2444_ = v___x_2451_;
goto v___jp_2438_;
}
}
else
{
v___y_2406_ = v___y_2447_;
v___y_2407_ = v___y_2448_;
v___y_2408_ = v___y_2449_;
goto v___jp_2405_;
}
}
v___jp_2456_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2461_ = lean_mk_empty_array_with_capacity(v_size_2459_);
lean_dec(v_size_2459_);
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_array_get_size(v_buckets_2460_);
v___x_2464_ = lean_nat_dec_lt(v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec_ref(v_buckets_2460_);
v___y_2447_ = v___y_2457_;
v___y_2448_ = v___y_2458_;
v___y_2449_ = v___x_2461_;
goto v___jp_2446_;
}
else
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_le(v___x_2463_, v___x_2463_);
if (v___x_2465_ == 0)
{
if (v___x_2464_ == 0)
{
lean_dec_ref(v_buckets_2460_);
v___y_2447_ = v___y_2457_;
v___y_2448_ = v___y_2458_;
v___y_2449_ = v___x_2461_;
goto v___jp_2446_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = ((size_t)0ULL);
v___x_2467_ = lean_usize_of_nat(v___x_2463_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2460_, v___x_2466_, v___x_2467_, v___x_2461_);
lean_dec_ref(v_buckets_2460_);
v___y_2447_ = v___y_2457_;
v___y_2448_ = v___y_2458_;
v___y_2449_ = v___x_2468_;
goto v___jp_2446_;
}
}
else
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = lean_usize_of_nat(v___x_2463_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2460_, v___x_2469_, v___x_2470_, v___x_2461_);
lean_dec_ref(v_buckets_2460_);
v___y_2447_ = v___y_2457_;
v___y_2448_ = v___y_2458_;
v___y_2449_ = v___x_2471_;
goto v___jp_2446_;
}
}
}
v___jp_2472_:
{
if (lean_obj_tag(v___y_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v_size_2477_; lean_object* v_buckets_2478_; 
v_a_2476_ = lean_ctor_get(v___y_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___y_2475_);
v_size_2477_ = lean_ctor_get(v_a_2476_, 0);
lean_inc(v_size_2477_);
v_buckets_2478_ = lean_ctor_get(v_a_2476_, 1);
lean_inc_ref(v_buckets_2478_);
lean_dec(v_a_2476_);
v___y_2457_ = v___y_2473_;
v___y_2458_ = v___y_2474_;
v_size_2459_ = v_size_2477_;
v_buckets_2460_ = v_buckets_2478_;
goto v___jp_2456_;
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
v_a_2479_ = lean_ctor_get(v___y_2475_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___y_2475_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___y_2475_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___y_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
v___jp_2487_:
{
lean_object* v_buckets_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v_buckets_2491_ = lean_ctor_get(v_results_2400_, 1);
v___x_2492_ = lean_unsigned_to_nat(0u);
v___x_2493_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
v___x_2494_ = lean_array_get_size(v_buckets_2491_);
v___x_2495_ = lean_nat_dec_lt(v___x_2492_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_dec(v_sp_2488_);
v___y_2457_ = v___y_2489_;
v___y_2458_ = v___y_2490_;
v_size_2459_ = v___x_2492_;
v_buckets_2460_ = v___x_2493_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_2497_ = lean_nat_dec_le(v___x_2494_, v___x_2494_);
if (v___x_2497_ == 0)
{
if (v___x_2495_ == 0)
{
lean_dec(v_sp_2488_);
v___y_2457_ = v___y_2489_;
v___y_2458_ = v___y_2490_;
v_size_2459_ = v___x_2492_;
v_buckets_2460_ = v___x_2493_;
goto v___jp_2456_;
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2494_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2401_, v_sp_2488_, v_buckets_2491_, v___x_2498_, v___x_2499_, v___x_2496_, v___y_2489_, v___y_2490_);
v___y_2473_ = v___y_2489_;
v___y_2474_ = v___y_2490_;
v___y_2475_ = v___x_2500_;
goto v___jp_2472_;
}
}
else
{
size_t v___x_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = lean_usize_of_nat(v___x_2494_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2401_, v_sp_2488_, v_buckets_2491_, v___x_2501_, v___x_2502_, v___x_2496_, v___y_2489_, v___y_2490_);
v___y_2473_ = v___y_2489_;
v___y_2474_ = v___y_2490_;
v___y_2475_ = v___x_2503_;
goto v___jp_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object* v_results_2520_, lean_object* v_useErrorFormat_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
uint8_t v_useErrorFormat_boxed_2525_; lean_object* v_res_2526_; 
v_useErrorFormat_boxed_2525_ = lean_unbox(v_useErrorFormat_2521_);
v_res_2526_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_results_2520_, v_useErrorFormat_boxed_2525_, v_a_2522_, v_a_2523_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec_ref(v_results_2520_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object* v_n_2527_, lean_object* v_as_2528_, lean_object* v_lo_2529_, lean_object* v_hi_2530_, lean_object* v_w_2531_, lean_object* v_hlo_2532_, lean_object* v_hhi_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2527_, v_as_2528_, v_lo_2529_, v_hi_2530_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object* v_n_2535_, lean_object* v_as_2536_, lean_object* v_lo_2537_, lean_object* v_hi_2538_, lean_object* v_w_2539_, lean_object* v_hlo_2540_, lean_object* v_hhi_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(v_n_2535_, v_as_2536_, v_lo_2537_, v_hi_2538_, v_w_2539_, v_hlo_2540_, v_hhi_2541_);
lean_dec(v_hi_2538_);
lean_dec(v_n_2535_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object* v_00_u03b2_2543_, lean_object* v_m_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2544_, v_a_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object* v_00_u03b2_2547_, lean_object* v_m_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(v_00_u03b2_2547_, v_m_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_m_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object* v_n_2551_, lean_object* v_lo_2552_, lean_object* v_hi_2553_, lean_object* v_hhi_2554_, lean_object* v_pivot_2555_, lean_object* v_as_2556_, lean_object* v_i_2557_, lean_object* v_k_2558_, lean_object* v_ilo_2559_, lean_object* v_ik_2560_, lean_object* v_w_2561_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2553_, v_pivot_2555_, v_as_2556_, v_i_2557_, v_k_2558_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object* v_n_2563_, lean_object* v_lo_2564_, lean_object* v_hi_2565_, lean_object* v_hhi_2566_, lean_object* v_pivot_2567_, lean_object* v_as_2568_, lean_object* v_i_2569_, lean_object* v_k_2570_, lean_object* v_ilo_2571_, lean_object* v_ik_2572_, lean_object* v_w_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(v_n_2563_, v_lo_2564_, v_hi_2565_, v_hhi_2566_, v_pivot_2567_, v_as_2568_, v_i_2569_, v_k_2570_, v_ilo_2571_, v_ik_2572_, v_w_2573_);
lean_dec(v_hi_2565_);
lean_dec(v_lo_2564_);
lean_dec(v_n_2563_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object* v_00_u03b2_2575_, lean_object* v_a_2576_, lean_object* v_x_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2576_, v_x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2579_, lean_object* v_a_2580_, lean_object* v_x_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(v_00_u03b2_2579_, v_a_2580_, v_x_2581_);
lean_dec(v_x_2581_);
lean_dec(v_a_2580_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t v_sz_2583_, size_t v_i_2584_, lean_object* v_bs_2585_){
_start:
{
uint8_t v___x_2586_; 
v___x_2586_ = lean_usize_dec_lt(v_i_2584_, v_sz_2583_);
if (v___x_2586_ == 0)
{
return v_bs_2585_;
}
else
{
lean_object* v_v_2587_; lean_object* v_snd_2588_; lean_object* v_size_2589_; lean_object* v___x_2590_; lean_object* v_bs_x27_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v_v_2587_ = lean_array_uget_borrowed(v_bs_2585_, v_i_2584_);
v_snd_2588_ = lean_ctor_get(v_v_2587_, 1);
v_size_2589_ = lean_ctor_get(v_snd_2588_, 0);
lean_inc(v_size_2589_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v_bs_x27_2591_ = lean_array_uset(v_bs_2585_, v_i_2584_, v___x_2590_);
v___x_2592_ = ((size_t)1ULL);
v___x_2593_ = lean_usize_add(v_i_2584_, v___x_2592_);
v___x_2594_ = lean_array_uset(v_bs_x27_2591_, v_i_2584_, v_size_2589_);
v_i_2584_ = v___x_2593_;
v_bs_2585_ = v___x_2594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object* v_sz_2596_, lean_object* v_i_2597_, lean_object* v_bs_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_boxed_2599_, v_i_boxed_2600_, v_bs_2598_);
return v_res_2601_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0));
v___x_2604_ = l_Lean_stringToMessageData(v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2));
v___x_2607_ = l_Lean_stringToMessageData(v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4));
v___x_2610_ = l_Lean_stringToMessageData(v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6));
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t v_useErrorFormat_2614_, uint8_t v_groupByFilename_2615_, uint8_t v_verbose_2616_, lean_object* v_as_2617_, size_t v_i_2618_, size_t v_stop_2619_, lean_object* v_b_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_a_2625_; lean_object* v_val_2630_; uint8_t v___x_2632_; 
v___x_2632_ = lean_usize_dec_eq(v_i_2618_, v_stop_2619_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2698_; 
v___x_2633_ = lean_array_uget(v_as_2617_, v_i_2618_);
v_fst_2634_ = lean_ctor_get(v___x_2633_, 0);
v_snd_2635_ = lean_ctor_get(v___x_2633_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2637_ = v___x_2633_;
v_isShared_2638_ = v_isSharedCheck_2698_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_snd_2635_);
lean_inc(v_fst_2634_);
lean_dec(v___x_2633_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2698_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_warnings_2640_; lean_object* v_size_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_size_2668_ = lean_ctor_get(v_snd_2635_, 0);
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2670_ = lean_nat_dec_eq(v_size_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
if (v_groupByFilename_2615_ == 0)
{
if (v_useErrorFormat_2614_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2672_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2635_, v___x_2671_, v_useErrorFormat_2614_, v___y_2621_, v___y_2622_);
lean_dec(v_snd_2635_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
v_warnings_2640_ = v_a_2673_;
goto v___jp_2639_;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_del_object(v___x_2637_);
lean_dec(v_fst_2634_);
lean_dec_ref(v_b_2620_);
v_a_2674_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2672_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2672_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
goto v___jp_2657_;
}
}
else
{
goto v___jp_2657_;
}
}
else
{
lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2695_; 
lean_del_object(v___x_2637_);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_snd_2635_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; lean_object* v_unused_2697_; 
v_unused_2696_ = lean_ctor_get(v_snd_2635_, 1);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_snd_2635_, 0);
lean_dec(v_unused_2697_);
v___x_2683_ = v_snd_2635_;
v_isShared_2684_ = v_isSharedCheck_2695_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v_snd_2635_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2695_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
uint8_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = 2;
v___x_2686_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_verbose_2616_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_del_object(v___x_2683_);
lean_dec(v_fst_2634_);
v_a_2625_ = v_b_2620_;
goto v___jp_2624_;
}
else
{
lean_object* v_toEnvLinter_2687_; lean_object* v_noErrorsFound_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v_toEnvLinter_2687_ = lean_ctor_get(v_fst_2634_, 0);
lean_inc_ref(v_toEnvLinter_2687_);
lean_dec(v_fst_2634_);
v_noErrorsFound_2688_ = lean_ctor_get(v_toEnvLinter_2687_, 1);
lean_inc_ref(v_noErrorsFound_2688_);
lean_dec_ref(v_toEnvLinter_2687_);
v___x_2689_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7);
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 7);
lean_ctor_set(v___x_2683_, 1, v_noErrorsFound_2688_);
lean_ctor_set(v___x_2683_, 0, v___x_2689_);
v___x_2691_ = v___x_2683_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_noErrorsFound_2688_);
v___x_2691_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v_val_2630_ = v___x_2693_;
goto v___jp_2629_;
}
}
}
}
v___jp_2639_:
{
lean_object* v_toEnvLinter_2641_; lean_object* v_name_2642_; lean_object* v_errorsFound_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v_toEnvLinter_2641_ = lean_ctor_get(v_fst_2634_, 0);
lean_inc_ref(v_toEnvLinter_2641_);
v_name_2642_ = lean_ctor_get(v_fst_2634_, 1);
lean_inc(v_name_2642_);
lean_dec(v_fst_2634_);
v_errorsFound_2643_ = lean_ctor_get(v_toEnvLinter_2641_, 2);
lean_inc_ref(v_errorsFound_2643_);
lean_dec_ref(v_toEnvLinter_2641_);
v___x_2644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1);
v___x_2645_ = l_Lean_MessageData_ofName(v_name_2642_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 7);
lean_ctor_set(v___x_2637_, 1, v___x_2645_);
lean_ctor_set(v___x_2637_, 0, v___x_2644_);
v___x_2647_ = v___x_2637_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v_errorsFound_2643_);
v___x_2651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v_warnings_2640_);
v___x_2654_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v_val_2630_ = v___x_2655_;
goto v___jp_2629_;
}
}
v___jp_2657_:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_snd_2635_, v_useErrorFormat_2614_, v___y_2621_, v___y_2622_);
lean_dec(v_snd_2635_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2658_);
v_warnings_2640_ = v_a_2659_;
goto v___jp_2639_;
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_del_object(v___x_2637_);
lean_dec(v_fst_2634_);
lean_dec_ref(v_b_2620_);
v_a_2660_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2658_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2658_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
}
else
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_b_2620_);
return v___x_2699_;
}
v___jp_2624_:
{
size_t v___x_2626_; size_t v___x_2627_; 
v___x_2626_ = ((size_t)1ULL);
v___x_2627_ = lean_usize_add(v_i_2618_, v___x_2626_);
v_i_2618_ = v___x_2627_;
v_b_2620_ = v_a_2625_;
goto _start;
}
v___jp_2629_:
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_array_push(v_b_2620_, v_val_2630_);
v_a_2625_ = v___x_2631_;
goto v___jp_2624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object* v_useErrorFormat_2700_, lean_object* v_groupByFilename_2701_, lean_object* v_verbose_2702_, lean_object* v_as_2703_, lean_object* v_i_2704_, lean_object* v_stop_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_useErrorFormat_boxed_2710_; uint8_t v_groupByFilename_boxed_2711_; uint8_t v_verbose_boxed_2712_; size_t v_i_boxed_2713_; size_t v_stop_boxed_2714_; lean_object* v_res_2715_; 
v_useErrorFormat_boxed_2710_ = lean_unbox(v_useErrorFormat_2700_);
v_groupByFilename_boxed_2711_ = lean_unbox(v_groupByFilename_2701_);
v_verbose_boxed_2712_ = lean_unbox(v_verbose_2702_);
v_i_boxed_2713_ = lean_unbox_usize(v_i_2704_);
lean_dec(v_i_2704_);
v_stop_boxed_2714_ = lean_unbox_usize(v_stop_2705_);
lean_dec(v_stop_2705_);
v_res_2715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_boxed_2710_, v_groupByFilename_boxed_2711_, v_verbose_boxed_2712_, v_as_2703_, v_i_boxed_2713_, v_stop_boxed_2714_, v_b_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec_ref(v_as_2703_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t v_useErrorFormat_2718_, uint8_t v_groupByFilename_2719_, uint8_t v_verbose_2720_, lean_object* v_as_2721_, lean_object* v_start_2722_, lean_object* v_stop_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0));
v___x_2728_ = lean_nat_dec_lt(v_start_2722_, v_stop_2723_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
return v___x_2729_;
}
else
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = lean_array_get_size(v_as_2721_);
v___x_2731_ = lean_nat_dec_le(v_stop_2723_, v___x_2730_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_nat_dec_lt(v_start_2722_, v___x_2730_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2727_);
return v___x_2733_;
}
else
{
size_t v___x_2734_; size_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_usize_of_nat(v_start_2722_);
v___x_2735_ = lean_usize_of_nat(v___x_2730_);
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2718_, v_groupByFilename_2719_, v_verbose_2720_, v_as_2721_, v___x_2734_, v___x_2735_, v___x_2727_, v___y_2724_, v___y_2725_);
return v___x_2736_;
}
}
else
{
size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_usize_of_nat(v_start_2722_);
v___x_2738_ = lean_usize_of_nat(v_stop_2723_);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2718_, v_groupByFilename_2719_, v_verbose_2720_, v_as_2721_, v___x_2737_, v___x_2738_, v___x_2727_, v___y_2724_, v___y_2725_);
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object* v_useErrorFormat_2740_, lean_object* v_groupByFilename_2741_, lean_object* v_verbose_2742_, lean_object* v_as_2743_, lean_object* v_start_2744_, lean_object* v_stop_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v_useErrorFormat_boxed_2749_; uint8_t v_groupByFilename_boxed_2750_; uint8_t v_verbose_boxed_2751_; lean_object* v_res_2752_; 
v_useErrorFormat_boxed_2749_ = lean_unbox(v_useErrorFormat_2740_);
v_groupByFilename_boxed_2750_ = lean_unbox(v_groupByFilename_2741_);
v_verbose_boxed_2751_ = lean_unbox(v_verbose_2742_);
v_res_2752_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_boxed_2749_, v_groupByFilename_boxed_2750_, v_verbose_boxed_2751_, v_as_2743_, v_start_2744_, v_stop_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v_stop_2745_);
lean_dec(v_start_2744_);
lean_dec_ref(v_as_2743_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object* v_as_2753_, size_t v_i_2754_, size_t v_stop_2755_, lean_object* v_b_2756_){
_start:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_usize_dec_eq(v_i_2754_, v_stop_2755_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; size_t v___x_2760_; size_t v___x_2761_; 
v___x_2758_ = lean_array_uget_borrowed(v_as_2753_, v_i_2754_);
v___x_2759_ = lean_nat_add(v_b_2756_, v___x_2758_);
lean_dec(v_b_2756_);
v___x_2760_ = ((size_t)1ULL);
v___x_2761_ = lean_usize_add(v_i_2754_, v___x_2760_);
v_i_2754_ = v___x_2761_;
v_b_2756_ = v___x_2759_;
goto _start;
}
else
{
return v_b_2756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object* v_as_2763_, lean_object* v_i_2764_, lean_object* v_stop_2765_, lean_object* v_b_2766_){
_start:
{
size_t v_i_boxed_2767_; size_t v_stop_boxed_2768_; lean_object* v_res_2769_; 
v_i_boxed_2767_ = lean_unbox_usize(v_i_2764_);
lean_dec(v_i_2764_);
v_stop_boxed_2768_ = lean_unbox_usize(v_stop_2765_);
lean_dec(v_stop_2765_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v_as_2763_, v_i_boxed_2767_, v_stop_boxed_2768_, v_b_2766_);
lean_dec_ref(v_as_2763_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object* v_as_2770_, size_t v_i_2771_, size_t v_stop_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_eq(v_i_2771_, v_stop_2772_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_array_uget_borrowed(v_as_2770_, v_i_2771_);
lean_inc(v___x_2777_);
v___x_2778_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v___x_2777_, v___y_2774_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v_a_2781_; uint8_t v___x_2785_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
v___x_2785_ = lean_unbox(v_a_2779_);
lean_dec(v_a_2779_);
if (v___x_2785_ == 0)
{
v_a_2781_ = v_b_2773_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2786_; 
lean_inc(v___x_2777_);
v___x_2786_ = lean_array_push(v_b_2773_, v___x_2777_);
v_a_2781_ = v___x_2786_;
goto v___jp_2780_;
}
v___jp_2780_:
{
size_t v___x_2782_; size_t v___x_2783_; 
v___x_2782_ = ((size_t)1ULL);
v___x_2783_ = lean_usize_add(v_i_2771_, v___x_2782_);
v_i_2771_ = v___x_2783_;
v_b_2773_ = v_a_2781_;
goto _start;
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_b_2773_);
v_a_2787_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2778_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2778_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v___x_2795_; 
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_b_2773_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object* v_as_2796_, lean_object* v_i_2797_, lean_object* v_stop_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
size_t v_i_boxed_2802_; size_t v_stop_boxed_2803_; lean_object* v_res_2804_; 
v_i_boxed_2802_ = lean_unbox_usize(v_i_2797_);
lean_dec(v_i_2797_);
v_stop_boxed_2803_ = lean_unbox_usize(v_stop_2798_);
lean_dec(v_stop_2798_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2796_, v_i_boxed_2802_, v_stop_boxed_2803_, v_b_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v_as_2796_);
return v_res_2804_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__0));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__2));
v___x_2810_ = l_Lean_stringToMessageData(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__4));
v___x_2813_ = l_Lean_stringToMessageData(v___x_2812_);
return v___x_2813_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__6));
v___x_2816_ = l_Lean_stringToMessageData(v___x_2815_);
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__8));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__10));
v___x_2822_ = l_Lean_stringToMessageData(v___x_2821_);
return v___x_2822_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__12));
v___x_2825_ = l_Lean_stringToMessageData(v___x_2824_);
return v___x_2825_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__14));
v___x_2828_ = l_Lean_stringToMessageData(v___x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object* v_results_2830_, lean_object* v_decls_2831_, uint8_t v_groupByFilename_2832_, lean_object* v_whereDesc_2833_, uint8_t v_runClippyLinters_2834_, uint8_t v_verbose_2835_, lean_object* v_numLinters_2836_, uint8_t v_useErrorFormat_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_s_2842_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = lean_array_get_size(v_results_2830_);
v___x_2849_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_2837_, v_groupByFilename_2832_, v_verbose_2835_, v_results_2830_, v___x_2847_, v___x_2848_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v_a_2902_; lean_object* v___y_2915_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = lean_array_to_list(v_a_2850_);
v___x_2852_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2853_ = l_Lean_MessageData_joinSep(v___x_2851_, v___x_2852_);
v___x_2854_ = lean_array_get_size(v_decls_2831_);
v___x_2925_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_2926_ = lean_nat_dec_lt(v___x_2847_, v___x_2854_);
if (v___x_2926_ == 0)
{
v_a_2902_ = v___x_2925_;
goto v___jp_2901_;
}
else
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_le(v___x_2854_, v___x_2854_);
if (v___x_2927_ == 0)
{
if (v___x_2926_ == 0)
{
v_a_2902_ = v___x_2925_;
goto v___jp_2901_;
}
else
{
size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = lean_usize_of_nat(v___x_2854_);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2831_, v___x_2928_, v___x_2929_, v___x_2925_, v_a_2839_);
v___y_2915_ = v___x_2930_;
goto v___jp_2914_;
}
}
else
{
size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2854_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2831_, v___x_2931_, v___x_2932_, v___x_2925_, v_a_2839_);
v___y_2915_ = v___x_2933_;
goto v___jp_2914_;
}
}
v___jp_2855_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_inc_ref(v___y_2858_);
v___x_2859_ = l_Lean_stringToMessageData(v___y_2858_);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2856_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__3, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = lean_nat_sub(v___x_2854_, v___y_2857_);
v___x_2864_ = l_Nat_reprFast(v___x_2863_);
v___x_2865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
v___x_2866_ = l_Lean_MessageData_ofFormat(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2862_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__5, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l_Nat_reprFast(v___y_2857_);
v___x_2871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
v___x_2872_ = l_Lean_MessageData_ofFormat(v___x_2871_);
v___x_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2869_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__7, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Lean_stringToMessageData(v_whereDesc_2833_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__9, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Nat_reprFast(v_numLinters_2836_);
v___x_2881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
v___x_2882_ = l_Lean_MessageData_ofFormat(v___x_2881_);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2879_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__11, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v___x_2853_);
v_s_2842_ = v___x_2886_;
goto v___jp_2841_;
}
v___jp_2887_:
{
if (v_verbose_2835_ == 0)
{
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v_numLinters_2836_);
lean_dec_ref(v_whereDesc_2833_);
v_s_2842_ = v___x_2853_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2890_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__13, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13);
lean_inc(v___y_2889_);
v___x_2891_ = l_Nat_reprFast(v___y_2889_);
v___x_2892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = l_Lean_MessageData_ofFormat(v___x_2892_);
v___x_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2890_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__15, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15);
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_unsigned_to_nat(1u);
v___x_2898_ = lean_nat_dec_eq(v___y_2889_, v___x_2897_);
lean_dec(v___y_2889_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
v___x_2899_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__16));
v___y_2856_ = v___x_2896_;
v___y_2857_ = v___y_2888_;
v___y_2858_ = v___x_2899_;
goto v___jp_2855_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___y_2856_ = v___x_2896_;
v___y_2857_ = v___y_2888_;
v___y_2858_ = v___x_2900_;
goto v___jp_2855_;
}
}
}
v___jp_2901_:
{
lean_object* v___x_2903_; size_t v_sz_2904_; size_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2903_ = lean_array_get_size(v_a_2902_);
lean_dec_ref(v_a_2902_);
v_sz_2904_ = lean_array_size(v_results_2830_);
v___x_2905_ = ((size_t)0ULL);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_2904_, v___x_2905_, v_results_2830_);
v___x_2907_ = lean_array_get_size(v___x_2906_);
v___x_2908_ = lean_nat_dec_lt(v___x_2847_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_dec_ref(v___x_2906_);
v___y_2888_ = v___x_2903_;
v___y_2889_ = v___x_2847_;
goto v___jp_2887_;
}
else
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_nat_dec_le(v___x_2907_, v___x_2907_);
if (v___x_2909_ == 0)
{
if (v___x_2908_ == 0)
{
lean_dec_ref(v___x_2906_);
v___y_2888_ = v___x_2903_;
v___y_2889_ = v___x_2847_;
goto v___jp_2887_;
}
else
{
size_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_usize_of_nat(v___x_2907_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_2906_, v___x_2905_, v___x_2910_, v___x_2847_);
lean_dec_ref(v___x_2906_);
v___y_2888_ = v___x_2903_;
v___y_2889_ = v___x_2911_;
goto v___jp_2887_;
}
}
else
{
size_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_usize_of_nat(v___x_2907_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_2906_, v___x_2905_, v___x_2912_, v___x_2847_);
lean_dec_ref(v___x_2906_);
v___y_2888_ = v___x_2903_;
v___y_2889_ = v___x_2913_;
goto v___jp_2887_;
}
}
}
v___jp_2914_:
{
if (lean_obj_tag(v___y_2915_) == 0)
{
lean_object* v_a_2916_; 
v_a_2916_ = lean_ctor_get(v___y_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref(v___y_2915_);
v_a_2902_ = v_a_2916_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v___x_2853_);
lean_dec(v_numLinters_2836_);
lean_dec_ref(v_whereDesc_2833_);
lean_dec_ref(v_results_2830_);
v_a_2917_ = lean_ctor_get(v___y_2915_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___y_2915_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___y_2915_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___y_2915_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_numLinters_2836_);
lean_dec_ref(v_whereDesc_2833_);
lean_dec_ref(v_results_2830_);
v_a_2934_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2849_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2849_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
v___jp_2841_:
{
if (v_runClippyLinters_2834_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__1, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_s_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v_s_2842_);
return v___x_2846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object* v_results_2942_, lean_object* v_decls_2943_, lean_object* v_groupByFilename_2944_, lean_object* v_whereDesc_2945_, lean_object* v_runClippyLinters_2946_, lean_object* v_verbose_2947_, lean_object* v_numLinters_2948_, lean_object* v_useErrorFormat_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
uint8_t v_groupByFilename_boxed_2953_; uint8_t v_runClippyLinters_boxed_2954_; uint8_t v_verbose_boxed_2955_; uint8_t v_useErrorFormat_boxed_2956_; lean_object* v_res_2957_; 
v_groupByFilename_boxed_2953_ = lean_unbox(v_groupByFilename_2944_);
v_runClippyLinters_boxed_2954_ = lean_unbox(v_runClippyLinters_2946_);
v_verbose_boxed_2955_ = lean_unbox(v_verbose_2947_);
v_useErrorFormat_boxed_2956_ = lean_unbox(v_useErrorFormat_2949_);
v_res_2957_ = l_Lean_Linter_EnvLinter_formatLinterResults(v_results_2942_, v_decls_2943_, v_groupByFilename_boxed_2953_, v_whereDesc_2945_, v_runClippyLinters_boxed_2954_, v_verbose_boxed_2955_, v_numLinters_2948_, v_useErrorFormat_boxed_2956_, v_a_2950_, v_a_2951_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec_ref(v_decls_2943_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object* v_as_2958_, size_t v_i_2959_, size_t v_stop_2960_, lean_object* v_b_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2958_, v_i_2959_, v_stop_2960_, v_b_2961_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object* v_as_2966_, lean_object* v_i_2967_, lean_object* v_stop_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
size_t v_i_boxed_2973_; size_t v_stop_boxed_2974_; lean_object* v_res_2975_; 
v_i_boxed_2973_ = lean_unbox_usize(v_i_2967_);
lean_dec(v_i_2967_);
v_stop_boxed_2974_ = lean_unbox_usize(v_stop_2968_);
lean_dec(v_stop_2968_);
v_res_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(v_as_2966_, v_i_boxed_2973_, v_stop_boxed_2974_, v_b_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec_ref(v_as_2966_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object* v_r_2976_, lean_object* v_k_2977_, lean_object* v_x_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_array_push(v_r_2976_, v_k_2977_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object* v_r_2980_, lean_object* v_k_2981_, lean_object* v_x_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(v_r_2980_, v_k_2981_, v_x_2982_);
lean_dec_ref(v_x_2982_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object* v_f_2984_, lean_object* v_x1_2985_, lean_object* v_x2_2986_, lean_object* v_x3_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_apply_3(v_f_2984_, v_x1_2985_, v_x2_2986_, v_x3_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2989_, lean_object* v_keys_2990_, lean_object* v_vals_2991_, lean_object* v_i_2992_, lean_object* v_acc_2993_){
_start:
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = lean_array_get_size(v_keys_2990_);
v___x_2995_ = lean_nat_dec_lt(v_i_2992_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_dec(v_i_2992_);
lean_dec(v_f_2989_);
return v_acc_2993_;
}
else
{
lean_object* v_k_2996_; lean_object* v_v_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_k_2996_ = lean_array_fget_borrowed(v_keys_2990_, v_i_2992_);
v_v_2997_ = lean_array_fget_borrowed(v_vals_2991_, v_i_2992_);
lean_inc(v_f_2989_);
lean_inc(v_v_2997_);
lean_inc(v_k_2996_);
v___x_2998_ = lean_apply_3(v_f_2989_, v_acc_2993_, v_k_2996_, v_v_2997_);
v___x_2999_ = lean_unsigned_to_nat(1u);
v___x_3000_ = lean_nat_add(v_i_2992_, v___x_2999_);
lean_dec(v_i_2992_);
v_i_2992_ = v___x_3000_;
v_acc_2993_ = v___x_2998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3002_, lean_object* v_keys_3003_, lean_object* v_vals_3004_, lean_object* v_i_3005_, lean_object* v_acc_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3002_, v_keys_3003_, v_vals_3004_, v_i_3005_, v_acc_3006_);
lean_dec_ref(v_vals_3004_);
lean_dec_ref(v_keys_3003_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3008_, lean_object* v_x_3009_, lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 0)
{
lean_object* v_es_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_es_3011_ = lean_ctor_get(v_x_3009_, 0);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_array_get_size(v_es_3011_);
v___x_3014_ = lean_nat_dec_lt(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec(v_f_3008_);
return v_x_3010_;
}
else
{
uint8_t v___x_3015_; 
v___x_3015_ = lean_nat_dec_le(v___x_3013_, v___x_3013_);
if (v___x_3015_ == 0)
{
if (v___x_3014_ == 0)
{
lean_dec(v_f_3008_);
return v_x_3010_;
}
else
{
size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3013_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3008_, v_es_3011_, v___x_3016_, v___x_3017_, v_x_3010_);
return v___x_3018_;
}
}
else
{
size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = ((size_t)0ULL);
v___x_3020_ = lean_usize_of_nat(v___x_3013_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3008_, v_es_3011_, v___x_3019_, v___x_3020_, v_x_3010_);
return v___x_3021_;
}
}
}
else
{
lean_object* v_ks_3022_; lean_object* v_vs_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_ks_3022_ = lean_ctor_get(v_x_3009_, 0);
v_vs_3023_ = lean_ctor_get(v_x_3009_, 1);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3008_, v_ks_3022_, v_vs_3023_, v___x_3024_, v_x_3010_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3026_, lean_object* v_as_3027_, size_t v_i_3028_, size_t v_stop_3029_, lean_object* v_b_3030_){
_start:
{
lean_object* v___y_3032_; uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_eq(v_i_3028_, v_stop_3029_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_array_uget_borrowed(v_as_3027_, v_i_3028_);
switch(lean_obj_tag(v___x_3037_))
{
case 0:
{
lean_object* v_key_3038_; lean_object* v_val_3039_; lean_object* v___x_3040_; 
v_key_3038_ = lean_ctor_get(v___x_3037_, 0);
v_val_3039_ = lean_ctor_get(v___x_3037_, 1);
lean_inc(v_f_3026_);
lean_inc(v_val_3039_);
lean_inc(v_key_3038_);
v___x_3040_ = lean_apply_3(v_f_3026_, v_b_3030_, v_key_3038_, v_val_3039_);
v___y_3032_ = v___x_3040_;
goto v___jp_3031_;
}
case 1:
{
lean_object* v_node_3041_; lean_object* v___x_3042_; 
v_node_3041_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_f_3026_);
v___x_3042_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3026_, v_node_3041_, v_b_3030_);
v___y_3032_ = v___x_3042_;
goto v___jp_3031_;
}
default: 
{
v___y_3032_ = v_b_3030_;
goto v___jp_3031_;
}
}
}
else
{
lean_dec(v_f_3026_);
return v_b_3030_;
}
v___jp_3031_:
{
size_t v___x_3033_; size_t v___x_3034_; 
v___x_3033_ = ((size_t)1ULL);
v___x_3034_ = lean_usize_add(v_i_3028_, v___x_3033_);
v_i_3028_ = v___x_3034_;
v_b_3030_ = v___y_3032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3043_, lean_object* v_as_3044_, lean_object* v_i_3045_, lean_object* v_stop_3046_, lean_object* v_b_3047_){
_start:
{
size_t v_i_boxed_3048_; size_t v_stop_boxed_3049_; lean_object* v_res_3050_; 
v_i_boxed_3048_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_stop_boxed_3049_ = lean_unbox_usize(v_stop_3046_);
lean_dec(v_stop_3046_);
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3043_, v_as_3044_, v_i_boxed_3048_, v_stop_boxed_3049_, v_b_3047_);
lean_dec_ref(v_as_3044_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3051_, v_x_3052_, v_x_3053_);
lean_dec_ref(v_x_3052_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object* v_map_3055_, lean_object* v_f_3056_, lean_object* v_init_3057_){
_start:
{
lean_object* v___f_3058_; lean_object* v___x_3059_; 
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3058_, 0, v_f_3056_);
v___x_3059_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v___f_3058_, v_map_3055_, v_init_3057_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object* v_map_3060_, lean_object* v_f_3061_, lean_object* v_init_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3060_, v_f_3061_, v_init_3062_);
lean_dec_ref(v_map_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3067_; lean_object* v_env_3068_; lean_object* v___x_3069_; lean_object* v_map_u2082_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3067_ = lean_st_ref_get(v_a_3065_);
v_env_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc_ref(v_env_3068_);
lean_dec(v___x_3067_);
v___x_3069_ = l_Lean_Environment_constants(v_env_3068_);
v_map_u2082_3070_ = lean_ctor_get(v___x_3069_, 1);
lean_inc_ref(v_map_u2082_3070_);
lean_dec_ref(v___x_3069_);
v___f_3071_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0));
v___x_3072_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_3073_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_u2082_3070_, v___f_3071_, v___x_3072_);
lean_dec_ref(v_map_u2082_3070_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3075_);
lean_dec(v_a_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule(v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object* v_00_u03c3_3086_, lean_object* v_00_u03b2_3087_, lean_object* v_map_3088_, lean_object* v_f_3089_, lean_object* v_init_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3088_, v_f_3089_, v_init_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object* v_00_u03c3_3092_, lean_object* v_00_u03b2_3093_, lean_object* v_map_3094_, lean_object* v_f_3095_, lean_object* v_init_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(v_00_u03c3_3092_, v_00_u03b2_3093_, v_map_3094_, v_f_3095_, v_init_3096_);
lean_dec_ref(v_map_3094_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object* v_map_3098_, lean_object* v_f_3099_, lean_object* v_init_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3099_, v_map_3098_, v_init_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object* v_map_3102_, lean_object* v_f_3103_, lean_object* v_init_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(v_map_3102_, v_f_3103_, v_init_3104_);
lean_dec_ref(v_map_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object* v_00_u03c3_3106_, lean_object* v_00_u03b2_3107_, lean_object* v_map_3108_, lean_object* v_f_3109_, lean_object* v_init_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3109_, v_map_3108_, v_init_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3112_, lean_object* v_00_u03b2_3113_, lean_object* v_map_3114_, lean_object* v_f_3115_, lean_object* v_init_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(v_00_u03c3_3112_, v_00_u03b2_3113_, v_map_3114_, v_f_3115_, v_init_3116_);
lean_dec_ref(v_map_3114_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3118_, lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v_f_3121_, lean_object* v_x_3122_, lean_object* v_x_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3121_, v_x_3122_, v_x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3125_, lean_object* v_00_u03b1_3126_, lean_object* v_00_u03b2_3127_, lean_object* v_f_3128_, lean_object* v_x_3129_, lean_object* v_x_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(v_00_u03c3_3125_, v_00_u03b1_3126_, v_00_u03b2_3127_, v_f_3128_, v_x_3129_, v_x_3130_);
lean_dec_ref(v_x_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3132_, lean_object* v_00_u03b2_3133_, lean_object* v_00_u03c3_3134_, lean_object* v_f_3135_, lean_object* v_as_3136_, size_t v_i_3137_, size_t v_stop_3138_, lean_object* v_b_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3135_, v_as_3136_, v_i_3137_, v_stop_3138_, v_b_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3141_, lean_object* v_00_u03b2_3142_, lean_object* v_00_u03c3_3143_, lean_object* v_f_3144_, lean_object* v_as_3145_, lean_object* v_i_3146_, lean_object* v_stop_3147_, lean_object* v_b_3148_){
_start:
{
size_t v_i_boxed_3149_; size_t v_stop_boxed_3150_; lean_object* v_res_3151_; 
v_i_boxed_3149_ = lean_unbox_usize(v_i_3146_);
lean_dec(v_i_3146_);
v_stop_boxed_3150_ = lean_unbox_usize(v_stop_3147_);
lean_dec(v_stop_3147_);
v_res_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3141_, v_00_u03b2_3142_, v_00_u03c3_3143_, v_f_3144_, v_as_3145_, v_i_boxed_3149_, v_stop_boxed_3150_, v_b_3148_);
lean_dec_ref(v_as_3145_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3152_, lean_object* v_00_u03b1_3153_, lean_object* v_00_u03b2_3154_, lean_object* v_f_3155_, lean_object* v_keys_3156_, lean_object* v_vals_3157_, lean_object* v_heq_3158_, lean_object* v_i_3159_, lean_object* v_acc_3160_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3155_, v_keys_3156_, v_vals_3157_, v_i_3159_, v_acc_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3162_, lean_object* v_00_u03b1_3163_, lean_object* v_00_u03b2_3164_, lean_object* v_f_3165_, lean_object* v_keys_3166_, lean_object* v_vals_3167_, lean_object* v_heq_3168_, lean_object* v_i_3169_, lean_object* v_acc_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3162_, v_00_u03b1_3163_, v_00_u03b2_3164_, v_f_3165_, v_keys_3166_, v_vals_3167_, v_heq_3168_, v_i_3169_, v_acc_3170_);
lean_dec_ref(v_vals_3167_);
lean_dec_ref(v_keys_3166_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object* v_x_3172_, lean_object* v_x_3173_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 0)
{
return v_x_3172_;
}
else
{
lean_object* v_key_3174_; lean_object* v_tail_3175_; lean_object* v___x_3176_; 
v_key_3174_ = lean_ctor_get(v_x_3173_, 0);
lean_inc(v_key_3174_);
v_tail_3175_ = lean_ctor_get(v_x_3173_, 2);
lean_inc(v_tail_3175_);
lean_dec_ref(v_x_3173_);
v___x_3176_ = lean_array_push(v_x_3172_, v_key_3174_);
v_x_3172_ = v___x_3176_;
v_x_3173_ = v_tail_3175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object* v_as_3178_, size_t v_i_3179_, size_t v_stop_3180_, lean_object* v_b_3181_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_eq(v_i_3179_, v_stop_3180_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; size_t v___x_3185_; size_t v___x_3186_; 
v___x_3183_ = lean_array_uget_borrowed(v_as_3178_, v_i_3179_);
lean_inc(v___x_3183_);
v___x_3184_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(v_b_3181_, v___x_3183_);
v___x_3185_ = ((size_t)1ULL);
v___x_3186_ = lean_usize_add(v_i_3179_, v___x_3185_);
v_i_3179_ = v___x_3186_;
v_b_3181_ = v___x_3184_;
goto _start;
}
else
{
return v_b_3181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object* v_as_3188_, lean_object* v_i_3189_, lean_object* v_stop_3190_, lean_object* v_b_3191_){
_start:
{
size_t v_i_boxed_3192_; size_t v_stop_boxed_3193_; lean_object* v_res_3194_; 
v_i_boxed_3192_ = lean_unbox_usize(v_i_3189_);
lean_dec(v_i_3189_);
v_stop_boxed_3193_ = lean_unbox_usize(v_stop_3190_);
lean_dec(v_stop_3190_);
v_res_3194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_as_3188_, v_i_boxed_3192_, v_stop_boxed_3193_, v_b_3191_);
lean_dec_ref(v_as_3188_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object* v_a_3195_){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_a_3199_; lean_object* v_env_3200_; lean_object* v___x_3201_; lean_object* v_map_u2081_3202_; lean_object* v_buckets_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; 
v___x_3197_ = lean_st_ref_get(v_a_3195_);
v___x_3198_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3195_);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
v_env_3200_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3197_);
v___x_3201_ = l_Lean_Environment_constants(v_env_3200_);
v_map_u2081_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc_ref(v_map_u2081_3202_);
lean_dec_ref(v___x_3201_);
v_buckets_3203_ = lean_ctor_get(v_map_u2081_3202_, 1);
lean_inc_ref(v_buckets_3203_);
lean_dec_ref(v_map_u2081_3202_);
v___x_3204_ = lean_unsigned_to_nat(0u);
v___x_3205_ = lean_array_get_size(v_buckets_3203_);
v___x_3206_ = lean_nat_dec_lt(v___x_3204_, v___x_3205_);
if (v___x_3206_ == 0)
{
lean_dec_ref(v_buckets_3203_);
lean_dec(v_a_3199_);
return v___x_3198_;
}
else
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_nat_dec_le(v___x_3205_, v___x_3205_);
if (v___x_3207_ == 0)
{
if (v___x_3206_ == 0)
{
lean_dec_ref(v_buckets_3203_);
lean_dec(v_a_3199_);
return v___x_3198_;
}
else
{
lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3217_; 
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3198_, 0);
lean_dec(v_unused_3218_);
v___x_3209_ = v___x_3198_;
v_isShared_3210_ = v_isSharedCheck_3217_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v___x_3198_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3217_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
size_t v___x_3211_; size_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3211_ = ((size_t)0ULL);
v___x_3212_ = lean_usize_of_nat(v___x_3205_);
v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3203_, v___x_3211_, v___x_3212_, v_a_3199_);
lean_dec_ref(v_buckets_3203_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3213_);
v___x_3215_ = v___x_3209_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3228_; 
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3198_, 0);
lean_dec(v_unused_3229_);
v___x_3220_ = v___x_3198_;
v_isShared_3221_ = v_isSharedCheck_3228_;
goto v_resetjp_3219_;
}
else
{
lean_dec(v___x_3198_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3228_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
size_t v___x_3222_; size_t v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3222_ = ((size_t)0ULL);
v___x_3223_ = lean_usize_of_nat(v___x_3205_);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3203_, v___x_3222_, v___x_3223_, v_a_3199_);
lean_dec_ref(v_buckets_3203_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3224_);
v___x_3226_ = v___x_3220_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3230_);
lean_dec(v_a_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Linter_EnvLinter_getAllDecls(v_a_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object* v_msg_3241_){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = lean_panic_fn_borrowed(v___x_3242_, v_msg_3241_);
return v___x_3243_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3247_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2));
v___x_3248_ = lean_unsigned_to_nat(14u);
v___x_3249_ = lean_unsigned_to_nat(22u);
v___x_3250_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1));
v___x_3251_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0));
v___x_3252_ = l_mkPanicMessageWithDecl(v___x_3251_, v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v_x_3255_, lean_object* v_x_3256_){
_start:
{
if (lean_obj_tag(v_x_3256_) == 0)
{
lean_dec_ref(v___x_3254_);
return v_x_3255_;
}
else
{
lean_object* v_key_3257_; lean_object* v_tail_3258_; uint8_t v___x_3259_; lean_object* v___y_3261_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_key_3257_ = lean_ctor_get(v_x_3256_, 0);
lean_inc(v_key_3257_);
v_tail_3258_ = lean_ctor_get(v_x_3256_, 2);
lean_inc(v_tail_3258_);
lean_dec_ref(v_x_3256_);
v___x_3259_ = 0;
lean_inc_ref(v___x_3254_);
v___x_3268_ = l_Lean_Environment_const2ModIdx(v___x_3254_);
v___x_3269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v___x_3268_, v_key_3257_);
lean_dec_ref(v___x_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3);
v___x_3271_ = l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(v___x_3270_);
v___y_3261_ = v___x_3271_;
goto v___jp_3260_;
}
else
{
lean_object* v_val_3272_; 
v_val_3272_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3272_);
lean_dec_ref(v___x_3269_);
v___y_3261_ = v_val_3272_;
goto v___jp_3260_;
}
v___jp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3262_ = lean_box(v___x_3259_);
v___x_3263_ = lean_array_get(v___x_3262_, v___x_3253_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec(v___x_3262_);
v___x_3264_ = lean_unbox(v___x_3263_);
lean_dec(v___x_3263_);
if (v___x_3264_ == 0)
{
lean_dec(v_key_3257_);
v_x_3256_ = v_tail_3258_;
goto _start;
}
else
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_array_push(v_x_3255_, v_key_3257_);
v_x_3255_ = v___x_3266_;
v_x_3256_ = v_tail_3258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3273_, v___x_3274_, v_x_3275_, v_x_3276_);
lean_dec_ref(v___x_3273_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object* v___x_3278_, lean_object* v___x_3279_, lean_object* v_as_3280_, size_t v_i_3281_, size_t v_stop_3282_, lean_object* v_b_3283_){
_start:
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_usize_dec_eq(v_i_3281_, v_stop_3282_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; size_t v___x_3287_; size_t v___x_3288_; 
v___x_3285_ = lean_array_uget_borrowed(v_as_3280_, v_i_3281_);
lean_inc(v___x_3285_);
lean_inc_ref(v___x_3279_);
v___x_3286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3278_, v___x_3279_, v_b_3283_, v___x_3285_);
v___x_3287_ = ((size_t)1ULL);
v___x_3288_ = lean_usize_add(v_i_3281_, v___x_3287_);
v_i_3281_ = v___x_3288_;
v_b_3283_ = v___x_3286_;
goto _start;
}
else
{
lean_dec_ref(v___x_3279_);
return v_b_3283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v_as_3292_, lean_object* v_i_3293_, lean_object* v_stop_3294_, lean_object* v_b_3295_){
_start:
{
size_t v_i_boxed_3296_; size_t v_stop_boxed_3297_; lean_object* v_res_3298_; 
v_i_boxed_3296_ = lean_unbox_usize(v_i_3293_);
lean_dec(v_i_3293_);
v_stop_boxed_3297_ = lean_unbox_usize(v_stop_3294_);
lean_dec(v_stop_3294_);
v_res_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3290_, v___x_3291_, v_as_3292_, v_i_boxed_3296_, v_stop_boxed_3297_, v_b_3295_);
lean_dec_ref(v_as_3292_);
lean_dec_ref(v___x_3290_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object* v_pkg_3299_, size_t v_sz_3300_, size_t v_i_3301_, lean_object* v_bs_3302_){
_start:
{
uint8_t v___x_3303_; 
v___x_3303_ = lean_usize_dec_lt(v_i_3301_, v_sz_3300_);
if (v___x_3303_ == 0)
{
return v_bs_3302_;
}
else
{
lean_object* v_v_3304_; lean_object* v___x_3305_; lean_object* v_bs_x27_3306_; uint8_t v___x_3307_; size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_v_3304_ = lean_array_uget(v_bs_3302_, v_i_3301_);
v___x_3305_ = lean_unsigned_to_nat(0u);
v_bs_x27_3306_ = lean_array_uset(v_bs_3302_, v_i_3301_, v___x_3305_);
v___x_3307_ = l_Lean_Name_isPrefixOf(v_pkg_3299_, v_v_3304_);
lean_dec(v_v_3304_);
v___x_3308_ = ((size_t)1ULL);
v___x_3309_ = lean_usize_add(v_i_3301_, v___x_3308_);
v___x_3310_ = lean_box(v___x_3307_);
v___x_3311_ = lean_array_uset(v_bs_x27_3306_, v_i_3301_, v___x_3310_);
v_i_3301_ = v___x_3309_;
v_bs_3302_ = v___x_3311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object* v_pkg_3313_, lean_object* v_sz_3314_, lean_object* v_i_3315_, lean_object* v_bs_3316_){
_start:
{
size_t v_sz_boxed_3317_; size_t v_i_boxed_3318_; lean_object* v_res_3319_; 
v_sz_boxed_3317_ = lean_unbox_usize(v_sz_3314_);
lean_dec(v_sz_3314_);
v_i_boxed_3318_ = lean_unbox_usize(v_i_3315_);
lean_dec(v_i_3315_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3313_, v_sz_boxed_3317_, v_i_boxed_3318_, v_bs_3316_);
lean_dec(v_pkg_3313_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object* v_pkg_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v_a_3325_; lean_object* v_env_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_map_u2081_3329_; lean_object* v_buckets_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3323_ = lean_st_ref_get(v_a_3321_);
v___x_3324_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3321_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
v_env_3326_ = lean_ctor_get(v___x_3323_, 0);
lean_inc_ref_n(v_env_3326_, 2);
lean_dec(v___x_3323_);
v___x_3327_ = l_Lean_Environment_header(v_env_3326_);
v___x_3328_ = l_Lean_Environment_constants(v_env_3326_);
v_map_u2081_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc_ref(v_map_u2081_3329_);
lean_dec_ref(v___x_3328_);
v_buckets_3330_ = lean_ctor_get(v_map_u2081_3329_, 1);
lean_inc_ref(v_buckets_3330_);
lean_dec_ref(v_map_u2081_3329_);
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_array_get_size(v_buckets_3330_);
v___x_3333_ = lean_nat_dec_lt(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_dec_ref(v_buckets_3330_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v_env_3326_);
lean_dec(v_a_3325_);
return v___x_3324_;
}
else
{
lean_object* v___x_3334_; size_t v_sz_3335_; size_t v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v___x_3334_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3327_);
v_sz_3335_ = lean_array_size(v___x_3334_);
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3320_, v_sz_3335_, v___x_3336_, v___x_3334_);
v___x_3338_ = lean_nat_dec_le(v___x_3332_, v___x_3332_);
if (v___x_3338_ == 0)
{
if (v___x_3333_ == 0)
{
lean_dec_ref(v___x_3337_);
lean_dec_ref(v_buckets_3330_);
lean_dec_ref(v_env_3326_);
lean_dec(v_a_3325_);
return v___x_3324_;
}
else
{
lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3347_; 
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v___x_3324_, 0);
lean_dec(v_unused_3348_);
v___x_3340_ = v___x_3324_;
v_isShared_3341_ = v_isSharedCheck_3347_;
goto v_resetjp_3339_;
}
else
{
lean_dec(v___x_3324_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3347_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
size_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3342_ = lean_usize_of_nat(v___x_3332_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3337_, v_env_3326_, v_buckets_3330_, v___x_3336_, v___x_3342_, v_a_3325_);
lean_dec_ref(v_buckets_3330_);
lean_dec_ref(v___x_3337_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3343_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3357_; 
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v___x_3324_, 0);
lean_dec(v_unused_3358_);
v___x_3350_ = v___x_3324_;
v_isShared_3351_ = v_isSharedCheck_3357_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v___x_3324_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3357_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
size_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3352_ = lean_usize_of_nat(v___x_3332_);
v___x_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3337_, v_env_3326_, v_buckets_3330_, v___x_3336_, v___x_3352_, v_a_3325_);
lean_dec_ref(v_buckets_3330_);
lean_dec_ref(v___x_3337_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3353_);
v___x_3355_ = v___x_3350_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object* v_pkg_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec(v_pkg_3359_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object* v_pkg_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3363_, v_a_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object* v_pkg_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Linter_EnvLinter_getDeclsInPackage(v_pkg_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_pkg_3368_);
return v_res_3372_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin);
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

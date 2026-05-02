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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintScope_default;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintScope;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintScope_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintScope(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintScope___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Linter.EnvLinter.LintScope.default"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Linter.EnvLinter.LintScope.clippy"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Linter.EnvLinter.LintScope.all"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value;
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
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "-- (non-default linters skipped)\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__1;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "-- (default linters skipped)\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__5;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " declarations (plus "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__7;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " automatically generated ones) "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__9;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__11;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " linters\n\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__12 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__13;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-- Found "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__14 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__15;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " error"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__16 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__17;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__18 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__18_value;
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
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(0u);
return v___x_146_;
}
case 1:
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(1u);
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(2u);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_boxed_150_; lean_object* v_res_151_; 
v_x_boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(uint8_t v_x_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx___boxed(lean_object* v_x_154_){
_start:
{
uint8_t v_x_4__boxed_155_; lean_object* v_res_156_; 
v_x_4__boxed_155_ = lean_unbox(v_x_154_);
v_res_156_ = l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(v_x_4__boxed_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(lean_object* v_k_157_){
_start:
{
lean_inc(v_k_157_);
return v_k_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg___boxed(lean_object* v_k_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(v_k_158_);
lean_dec(v_k_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim(lean_object* v_motive_160_, lean_object* v_ctorIdx_161_, uint8_t v_t_162_, lean_object* v_h_163_, lean_object* v_k_164_){
_start:
{
lean_inc(v_k_164_);
return v_k_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___boxed(lean_object* v_motive_165_, lean_object* v_ctorIdx_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_k_169_){
_start:
{
uint8_t v_t_boxed_170_; lean_object* v_res_171_; 
v_t_boxed_170_ = lean_unbox(v_t_167_);
v_res_171_ = l_Lean_Linter_EnvLinter_LintScope_ctorElim(v_motive_165_, v_ctorIdx_166_, v_t_boxed_170_, v_h_168_, v_k_169_);
lean_dec(v_k_169_);
lean_dec(v_ctorIdx_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(lean_object* v_default_172_){
_start:
{
lean_inc(v_default_172_);
return v_default_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg___boxed(lean_object* v_default_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(v_default_173_);
lean_dec(v_default_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim(lean_object* v_motive_175_, uint8_t v_t_176_, lean_object* v_h_177_, lean_object* v_default_178_){
_start:
{
lean_inc(v_default_178_);
return v_default_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___boxed(lean_object* v_motive_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_default_182_){
_start:
{
uint8_t v_t_boxed_183_; lean_object* v_res_184_; 
v_t_boxed_183_ = lean_unbox(v_t_180_);
v_res_184_ = l_Lean_Linter_EnvLinter_LintScope_default_elim(v_motive_179_, v_t_boxed_183_, v_h_181_, v_default_182_);
lean_dec(v_default_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim___redArg(lean_object* v_clippy_185_){
_start:
{
lean_inc(v_clippy_185_);
return v_clippy_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim___redArg___boxed(lean_object* v_clippy_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Linter_EnvLinter_LintScope_clippy_elim___redArg(v_clippy_186_);
lean_dec(v_clippy_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim(lean_object* v_motive_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_clippy_191_){
_start:
{
lean_inc(v_clippy_191_);
return v_clippy_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_clippy_elim___boxed(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_clippy_195_){
_start:
{
uint8_t v_t_boxed_196_; lean_object* v_res_197_; 
v_t_boxed_196_ = lean_unbox(v_t_193_);
v_res_197_ = l_Lean_Linter_EnvLinter_LintScope_clippy_elim(v_motive_192_, v_t_boxed_196_, v_h_194_, v_clippy_195_);
lean_dec(v_clippy_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(lean_object* v_all_198_){
_start:
{
lean_inc(v_all_198_);
return v_all_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg___boxed(lean_object* v_all_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(v_all_199_);
lean_dec(v_all_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim(lean_object* v_motive_201_, uint8_t v_t_202_, lean_object* v_h_203_, lean_object* v_all_204_){
_start:
{
lean_inc(v_all_204_);
return v_all_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___boxed(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_all_208_){
_start:
{
uint8_t v_t_boxed_209_; lean_object* v_res_210_; 
v_t_boxed_209_ = lean_unbox(v_t_206_);
v_res_210_ = l_Lean_Linter_EnvLinter_LintScope_all_elim(v_motive_205_, v_t_boxed_209_, v_h_207_, v_all_208_);
lean_dec(v_all_208_);
return v_res_210_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope_default(void){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope(void){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintScope_ofNat(lean_object* v_n_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_le(v_n_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_dec_le(v_n_213_, v___x_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 2;
return v___x_218_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 1;
return v___x_219_;
}
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ofNat___boxed(lean_object* v_n_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_Linter_EnvLinter_LintScope_ofNat(v_n_221_);
lean_dec(v_n_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintScope(uint8_t v_x_224_, uint8_t v_y_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_224_);
v___x_227_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_y_225_);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintScope___boxed(lean_object* v_x_229_, lean_object* v_y_230_){
_start:
{
uint8_t v_x_13__boxed_231_; uint8_t v_y_14__boxed_232_; uint8_t v_res_233_; lean_object* v_r_234_; 
v_x_13__boxed_231_ = lean_unbox(v_x_229_);
v_y_14__boxed_232_ = lean_unbox(v_y_230_);
v_res_233_ = l_Lean_Linter_EnvLinter_instDecidableEqLintScope(v_x_13__boxed_231_, v_y_14__boxed_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr(uint8_t v_x_244_, lean_object* v_prec_245_){
_start:
{
lean_object* v___y_247_; lean_object* v___y_254_; lean_object* v___y_261_; 
switch(v_x_244_)
{
case 0:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1024u);
v___x_268_ = lean_nat_dec_le(v___x_267_, v_prec_245_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_247_ = v___x_269_;
goto v___jp_246_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_247_ = v___x_270_;
goto v___jp_246_;
}
}
case 1:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1024u);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_prec_245_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_254_ = v___x_273_;
goto v___jp_253_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_254_ = v___x_274_;
goto v___jp_253_;
}
}
default: 
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_prec_245_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_261_ = v___x_277_;
goto v___jp_260_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_261_ = v___x_278_;
goto v___jp_260_;
}
}
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_248_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1));
lean_inc(v___y_247_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___y_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = 0;
v___x_251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_250_);
v___x_252_ = l_Repr_addAppParen(v___x_251_, v_prec_245_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3));
lean_inc(v___y_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___y_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
v___x_259_ = l_Repr_addAppParen(v___x_258_, v_prec_245_);
return v___x_259_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5));
lean_inc(v___y_261_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_245_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed(lean_object* v_x_279_, lean_object* v_prec_280_){
_start:
{
uint8_t v_x_173__boxed_281_; lean_object* v_res_282_; 
v_x_173__boxed_281_ = lean_unbox(v_x_279_);
v_res_282_ = l_Lean_Linter_EnvLinter_instReprLintScope_repr(v_x_173__boxed_281_, v_prec_280_);
lean_dec(v_prec_280_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(lean_object* v_x1_285_, lean_object* v_x2_286_){
_start:
{
lean_object* v_name_287_; lean_object* v_name_288_; uint8_t v___x_289_; 
v_name_287_ = lean_ctor_get(v_x1_285_, 1);
v_name_288_ = lean_ctor_get(v_x2_286_, 1);
v___x_289_ = l_Lean_Name_lt(v_name_287_, v_name_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0___boxed(lean_object* v_x1_290_, lean_object* v_x2_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_x1_290_, v_x2_291_);
lean_dec_ref(v_x2_291_);
lean_dec_ref(v_x1_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(lean_object* v_a_294_, lean_object* v_as_295_, lean_object* v_k_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_mid_301_; lean_object* v_midVal_302_; uint8_t v___x_303_; 
v___x_299_ = lean_nat_add(v_x_297_, v_x_298_);
v___x_300_ = lean_unsigned_to_nat(1u);
v_mid_301_ = lean_nat_shiftr(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
v_midVal_302_ = lean_array_fget_borrowed(v_as_295_, v_mid_301_);
v___x_303_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_midVal_302_, v_k_296_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
lean_dec(v_x_298_);
v___x_304_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_296_, v_midVal_302_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
lean_dec(v_x_297_);
v___x_305_ = lean_array_get_size(v_as_295_);
v___x_306_ = lean_nat_dec_lt(v_mid_301_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_mid_301_);
lean_dec_ref(v_a_294_);
return v_as_295_;
}
else
{
lean_object* v___x_307_; lean_object* v_xs_x27_308_; lean_object* v___x_309_; 
v___x_307_ = lean_box(0);
v_xs_x27_308_ = lean_array_fset(v_as_295_, v_mid_301_, v___x_307_);
v___x_309_ = lean_array_fset(v_xs_x27_308_, v_mid_301_, v_a_294_);
lean_dec(v_mid_301_);
return v___x_309_;
}
}
else
{
v_x_298_ = v_mid_301_;
goto _start;
}
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_eq(v_mid_301_, v_x_297_);
if (v___x_311_ == 0)
{
lean_dec(v_x_297_);
v_x_297_ = v_mid_301_;
goto _start;
}
else
{
lean_object* v___x_313_; lean_object* v_j_314_; lean_object* v_as_315_; lean_object* v___x_316_; 
lean_dec(v_mid_301_);
lean_dec(v_x_298_);
v___x_313_ = lean_nat_add(v_x_297_, v___x_300_);
lean_dec(v_x_297_);
v_j_314_ = lean_array_get_size(v_as_295_);
v_as_315_ = lean_array_push(v_as_295_, v_a_294_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_313_, v_as_315_, v_j_314_);
lean_dec(v___x_313_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg___boxed(lean_object* v_a_317_, lean_object* v_as_318_, lean_object* v_k_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_317_, v_as_318_, v_k_319_, v_x_320_, v_x_321_);
lean_dec_ref(v_k_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(lean_object* v_a_323_, lean_object* v_as_324_, lean_object* v_k_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_array_get_size(v_as_324_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_nat_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_array_fget_borrowed(v_as_324_, v___x_327_);
v___x_330_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_325_, v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v___x_329_, v_k_325_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_lt(v___x_327_, v___x_326_);
if (v___x_332_ == 0)
{
lean_dec_ref(v_a_323_);
return v_as_324_;
}
else
{
lean_object* v___x_333_; lean_object* v_xs_x27_334_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
v_xs_x27_334_ = lean_array_fset(v_as_324_, v___x_327_, v___x_333_);
v___x_335_ = lean_array_fset(v_xs_x27_334_, v___x_327_, v_a_323_);
return v___x_335_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v___x_326_, v___x_336_);
v___x_338_ = lean_array_fget_borrowed(v_as_324_, v___x_337_);
v___x_339_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v___x_338_, v_k_325_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_325_, v___x_338_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = lean_nat_dec_lt(v___x_337_, v___x_326_);
if (v___x_341_ == 0)
{
lean_dec(v___x_337_);
lean_dec_ref(v_a_323_);
return v_as_324_;
}
else
{
lean_object* v___x_342_; lean_object* v_xs_x27_343_; lean_object* v___x_344_; 
v___x_342_ = lean_box(0);
v_xs_x27_343_ = lean_array_fset(v_as_324_, v___x_337_, v___x_342_);
v___x_344_ = lean_array_fset(v_xs_x27_343_, v___x_337_, v_a_323_);
lean_dec(v___x_337_);
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_323_, v_as_324_, v_k_325_, v___x_327_, v___x_337_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec(v___x_337_);
v___x_346_ = lean_array_push(v_as_324_, v_a_323_);
return v___x_346_;
}
}
}
else
{
lean_object* v_as_347_; lean_object* v___x_348_; 
v_as_347_ = lean_array_push(v_as_324_, v_a_323_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_327_, v_as_347_, v___x_326_);
return v___x_348_;
}
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_array_push(v_as_324_, v_a_323_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___boxed(lean_object* v_a_350_, lean_object* v_as_351_, lean_object* v_k_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(v_a_350_, v_as_351_, v_k_352_);
lean_dec_ref(v_k_352_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(lean_object* v_a_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
else
{
lean_object* v_head_357_; lean_object* v_tail_358_; uint8_t v___x_359_; 
v_head_357_ = lean_ctor_get(v_x_355_, 0);
v_tail_358_ = lean_ctor_get(v_x_355_, 1);
v___x_359_ = lean_name_eq(v_a_354_, v_head_357_);
if (v___x_359_ == 0)
{
v_x_355_ = v_tail_358_;
goto _start;
}
else
{
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1___boxed(lean_object* v_a_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_a_361_, v_x_362_);
lean_dec(v_x_362_);
lean_dec(v_a_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(lean_object* v_runOnly_365_, uint8_t v_scope_366_, lean_object* v_init_367_, lean_object* v_x_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_d_373_; 
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_k_376_; lean_object* v_v_377_; lean_object* v_l_378_; lean_object* v_r_379_; lean_object* v___y_381_; lean_object* v___x_386_; 
v_k_376_ = lean_ctor_get(v_x_368_, 1);
lean_inc(v_k_376_);
v_v_377_ = lean_ctor_get(v_x_368_, 2);
lean_inc(v_v_377_);
v_l_378_ = lean_ctor_get(v_x_368_, 3);
lean_inc(v_l_378_);
v_r_379_ = lean_ctor_get(v_x_368_, 4);
lean_inc(v_r_379_);
lean_dec_ref(v_x_368_);
v___x_386_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_365_, v_scope_366_, v_init_367_, v_l_378_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v_a_388_; 
lean_dec_ref(v___x_386_);
lean_dec(v_r_379_);
lean_dec(v_v_377_);
lean_dec(v_k_376_);
v_a_388_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v_a_387_);
v_d_373_ = v_a_388_;
goto v___jp_372_;
}
else
{
lean_object* v_a_389_; lean_object* v_fst_390_; lean_object* v_snd_391_; uint8_t v___y_406_; 
v_a_389_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_a_389_);
lean_dec_ref(v_a_387_);
v_fst_390_ = lean_ctor_get(v_v_377_, 0);
lean_inc(v_fst_390_);
v_snd_391_ = lean_ctor_get(v_v_377_, 1);
lean_inc(v_snd_391_);
lean_dec(v_v_377_);
if (lean_obj_tag(v_runOnly_365_) == 0)
{
switch(v_scope_366_)
{
case 0:
{
uint8_t v___x_407_; 
v___x_407_ = lean_unbox(v_snd_391_);
lean_dec(v_snd_391_);
v___y_406_ = v___x_407_;
goto v___jp_405_;
}
case 1:
{
uint8_t v___x_408_; 
v___x_408_ = lean_unbox(v_snd_391_);
lean_dec(v_snd_391_);
if (v___x_408_ == 0)
{
lean_dec_ref(v___x_386_);
goto v___jp_392_;
}
else
{
lean_dec(v_fst_390_);
lean_dec(v_a_389_);
lean_dec(v_k_376_);
v___y_381_ = v___x_386_;
goto v___jp_380_;
}
}
default: 
{
lean_dec(v_snd_391_);
lean_dec_ref(v___x_386_);
goto v___jp_392_;
}
}
}
else
{
lean_object* v_val_409_; uint8_t v___x_410_; 
lean_dec(v_snd_391_);
v_val_409_ = lean_ctor_get(v_runOnly_365_, 0);
v___x_410_ = l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_k_376_, v_val_409_);
v___y_406_ = v___x_410_;
goto v___jp_405_;
}
v___jp_392_:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_k_376_, v_fst_390_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc_n(v_a_394_, 2);
lean_dec_ref(v___x_393_);
v___x_395_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(v_a_394_, v_a_389_, v_a_394_);
lean_dec(v_a_394_);
v_init_367_ = v___x_395_;
v_x_368_ = v_r_379_;
goto _start;
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_a_389_);
lean_dec(v_r_379_);
v_a_397_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_393_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
v___jp_405_:
{
if (v___y_406_ == 0)
{
lean_dec(v_fst_390_);
lean_dec(v_a_389_);
lean_dec(v_k_376_);
v___y_381_ = v___x_386_;
goto v___jp_380_;
}
else
{
lean_dec_ref(v___x_386_);
goto v___jp_392_;
}
}
}
}
else
{
lean_dec(v_r_379_);
lean_dec(v_v_377_);
lean_dec(v_k_376_);
return v___x_386_;
}
v___jp_380_:
{
if (lean_obj_tag(v___y_381_) == 0)
{
lean_object* v_a_382_; 
v_a_382_ = lean_ctor_get(v___y_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v___y_381_);
if (lean_obj_tag(v_a_382_) == 0)
{
lean_object* v_a_383_; 
lean_dec(v_r_379_);
v_a_383_ = lean_ctor_get(v_a_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v_a_382_);
v_d_373_ = v_a_383_;
goto v___jp_372_;
}
else
{
lean_object* v_a_384_; 
v_a_384_ = lean_ctor_get(v_a_382_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v_a_382_);
v_init_367_ = v_a_384_;
v_x_368_ = v_r_379_;
goto _start;
}
}
else
{
lean_dec(v_r_379_);
return v___y_381_;
}
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_init_367_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_d_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2___boxed(lean_object* v_runOnly_413_, lean_object* v_scope_414_, lean_object* v_init_415_, lean_object* v_x_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v_scope_boxed_420_; lean_object* v_res_421_; 
v_scope_boxed_420_ = lean_unbox(v_scope_414_);
v_res_421_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_413_, v_scope_boxed_420_, v_init_415_, v_x_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_runOnly_413_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t v_scope_424_, lean_object* v_runOnly_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; lean_object* v_env_430_; lean_object* v___x_431_; lean_object* v_toEnvExtension_432_; lean_object* v_asyncMode_433_; lean_object* v___x_434_; lean_object* v_result_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_429_ = lean_st_ref_get(v_a_427_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_env_430_);
lean_dec(v___x_429_);
v___x_431_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_432_ = lean_ctor_get(v___x_431_, 0);
v_asyncMode_433_ = lean_ctor_get(v_toEnvExtension_432_, 2);
v___x_434_ = lean_box(1);
v_result_435_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getChecks___closed__0));
v___x_436_ = lean_box(0);
v___x_437_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_434_, v___x_431_, v_env_430_, v_asyncMode_433_, v___x_436_);
v___x_438_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_425_, v_scope_424_, v_result_435_, v___x_437_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_a_443_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_a_443_);
lean_dec(v_a_439_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v_a_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_438_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_438_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks___boxed(lean_object* v_scope_456_, lean_object* v_runOnly_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_scope_boxed_461_; lean_object* v_res_462_; 
v_scope_boxed_461_ = lean_unbox(v_scope_456_);
v_res_462_ = l_Lean_Linter_EnvLinter_getChecks(v_scope_boxed_461_, v_runOnly_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_runOnly_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(lean_object* v_a_463_, lean_object* v_as_464_, lean_object* v_k_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_463_, v_as_464_, v_k_465_, v_x_466_, v_x_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___boxed(lean_object* v_a_471_, lean_object* v_as_472_, lean_object* v_k_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(v_a_471_, v_as_472_, v_k_473_, v_x_474_, v_x_475_, v_x_476_, v_x_477_);
lean_dec_ref(v_k_473_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(lean_object* v_a_479_, lean_object* v_as_480_, size_t v_i_481_, size_t v_stop_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_eq(v_i_481_, v_stop_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_array_uget_borrowed(v_as_480_, v_i_481_);
v___x_485_ = lean_name_eq(v_a_479_, v___x_484_);
if (v___x_485_ == 0)
{
size_t v___x_486_; size_t v___x_487_; 
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_481_, v___x_486_);
v_i_481_ = v___x_487_;
goto _start;
}
else
{
return v___x_485_;
}
}
else
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8___boxed(lean_object* v_a_490_, lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_){
_start:
{
size_t v_i_boxed_494_; size_t v_stop_boxed_495_; uint8_t v_res_496_; lean_object* v_r_497_; 
v_i_boxed_494_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_495_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_490_, v_as_491_, v_i_boxed_494_, v_stop_boxed_495_);
lean_dec_ref(v_as_491_);
lean_dec(v_a_490_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(lean_object* v_as_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_array_get_size(v_as_498_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
return v___x_502_;
}
else
{
if (v___x_502_ == 0)
{
return v___x_502_;
}
else
{
size_t v___x_503_; size_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = ((size_t)0ULL);
v___x_504_ = lean_usize_of_nat(v___x_501_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_499_, v_as_498_, v___x_503_, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6___boxed(lean_object* v_as_506_, lean_object* v_a_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v_as_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_as_506_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Array_instInhabited(lean_box(0));
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(lean_object* v_linter_513_, lean_object* v_decl_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v___y_519_; lean_object* v_env_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_517_ = lean_st_ref_get(v___y_515_);
v_env_527_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_env_527_);
lean_dec(v___x_517_);
v___x_528_ = lean_obj_once(&l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0, &l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once, _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0);
v___x_529_ = l_Lean_Linter_EnvLinter_builtinNolintAttr;
v___x_530_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_528_, v___x_529_, v_env_527_, v_decl_514_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_531_; 
v___x_531_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___y_519_ = v___x_531_;
goto v___jp_518_;
}
else
{
lean_object* v_val_532_; 
v_val_532_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_532_);
lean_dec_ref(v___x_530_);
v___y_519_ = v_val_532_;
goto v___jp_518_;
}
v___jp_518_:
{
uint8_t v___x_520_; 
v___x_520_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v___y_519_, v_linter_513_);
lean_dec_ref(v___y_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = 1;
v___x_522_ = lean_box(v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
else
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = 0;
v___x_525_ = lean_box(v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___boxed(lean_object* v_linter_533_, lean_object* v_decl_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_533_, v_decl_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec(v_linter_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object* v___x_538_, lean_object* v_as_539_, size_t v_i_540_, size_t v_stop_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_usize_dec_eq(v_i_540_, v_stop_541_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_array_uget_borrowed(v_as_539_, v_i_540_);
lean_inc(v___x_547_);
v___x_548_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v___x_538_, v___x_547_, v___y_544_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_a_551_; uint8_t v___x_555_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v___x_555_ = lean_unbox(v_a_549_);
lean_dec(v_a_549_);
if (v___x_555_ == 0)
{
v_a_551_ = v_b_542_;
goto v___jp_550_;
}
else
{
lean_object* v___x_556_; 
lean_inc(v___x_547_);
v___x_556_ = lean_array_push(v_b_542_, v___x_547_);
v_a_551_ = v___x_556_;
goto v___jp_550_;
}
v___jp_550_:
{
size_t v___x_552_; size_t v___x_553_; 
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_add(v_i_540_, v___x_552_);
v_i_540_ = v___x_553_;
v_b_542_ = v_a_551_;
goto _start;
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v_b_542_);
v_a_557_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_548_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_548_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_b_542_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object* v___x_566_, lean_object* v_as_567_, lean_object* v_i_568_, lean_object* v_stop_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v_i_boxed_574_; size_t v_stop_boxed_575_; lean_object* v_res_576_; 
v_i_boxed_574_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_stop_boxed_575_ = lean_unbox_usize(v_stop_569_);
lean_dec(v_stop_569_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v___x_566_, v_as_567_, v_i_boxed_574_, v_stop_boxed_575_, v_b_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_as_567_);
lean_dec(v___x_566_);
return v_res_576_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_581_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v___x_580_);
lean_ctor_set(v___x_581_, 4, v___x_580_);
lean_ctor_set(v___x_581_, 5, v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(32u);
v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
lean_ctor_set(v___x_586_, 2, v___x_585_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
lean_ctor_set(v___x_586_, 4, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v_test_589_, lean_object* v_v_590_, lean_object* v_x_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; size_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
lean_inc_n(v___x_587_, 5);
v___x_596_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_596_, 0, v___x_587_);
lean_ctor_set(v___x_596_, 1, v___x_587_);
lean_ctor_set(v___x_596_, 2, v___x_587_);
lean_ctor_set(v___x_596_, 3, v___x_587_);
lean_ctor_set(v___x_596_, 4, v___x_595_);
lean_ctor_set(v___x_596_, 5, v___x_595_);
lean_ctor_set(v___x_596_, 6, v___x_595_);
lean_ctor_set(v___x_596_, 7, v___x_595_);
lean_ctor_set(v___x_596_, 8, v___x_595_);
lean_ctor_set(v___x_596_, 9, v___x_595_);
v___x_597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2);
v___x_598_ = lean_unsigned_to_nat(32u);
v___x_599_ = lean_mk_empty_array_with_capacity(v___x_598_);
v___x_600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3);
v___x_601_ = ((size_t)5ULL);
v___x_602_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_599_);
lean_ctor_set(v___x_602_, 2, v___x_587_);
lean_ctor_set(v___x_602_, 3, v___x_587_);
lean_ctor_set_usize(v___x_602_, 4, v___x_601_);
v___x_603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4);
v___x_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_604_, 0, v___x_596_);
lean_ctor_set(v___x_604_, 1, v___x_597_);
lean_ctor_set(v___x_604_, 2, v___x_588_);
lean_ctor_set(v___x_604_, 3, v___x_602_);
lean_ctor_set(v___x_604_, 4, v___x_603_);
v___x_605_ = lean_st_mk_ref(v___x_604_);
v___x_606_ = l_Lean_Elab_Command_mkMetaContext;
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
lean_inc(v___x_605_);
v___x_607_ = lean_apply_6(v_test_589_, v_v_590_, v___x_606_, v___x_605_, v___y_592_, v___y_593_, lean_box(0));
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_616_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_st_ref_get(v___x_605_);
lean_dec(v___x_605_);
lean_dec(v___x_612_);
if (v_isShared_611_ == 0)
{
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_608_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_dec(v___x_605_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v_test_619_, lean_object* v_v_620_, lean_object* v_x_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(v___x_617_, v___x_618_, v_test_619_, v_v_620_, v_x_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object* v_a_626_, lean_object* v___x_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_apply_2(v_a_626_, v___x_627_, lean_box(0));
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_a_638_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object* v_a_646_, lean_object* v___x_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(v_a_646_, v___x_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object* v_linter_650_, size_t v_sz_651_, size_t v_i_652_, lean_object* v_bs_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_linter_650_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_bs_653_);
return v___x_658_;
}
else
{
lean_object* v_toEnvLinter_659_; lean_object* v_test_660_; lean_object* v_v_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_toEnvLinter_659_ = lean_ctor_get(v_linter_650_, 0);
v_test_660_ = lean_ctor_get(v_toEnvLinter_659_, 0);
v_v_661_ = lean_array_uget(v_bs_653_, v_i_652_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_box(1);
lean_inc(v_v_661_);
lean_inc_ref(v_test_660_);
v___f_664_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed), 8, 4);
lean_closure_set(v___f_664_, 0, v___x_662_);
lean_closure_set(v___f_664_, 1, v___x_663_);
lean_closure_set(v___f_664_, 2, v_test_660_);
lean_closure_set(v___f_664_, 3, v_v_661_);
v___x_665_ = lean_box(0);
v___x_666_ = l_Lean_Core_wrapAsync___redArg(v___f_664_, v___x_665_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___f_669_; lean_object* v___x_670_; lean_object* v_bs_x27_671_; lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = lean_box(0);
v___f_669_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_669_, 0, v_a_667_);
lean_closure_set(v___f_669_, 1, v___x_668_);
v___x_670_ = lean_io_as_task(v___f_669_, v___x_662_);
v_bs_x27_671_ = lean_array_uset(v_bs_653_, v_i_652_, v___x_662_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_v_661_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_652_, v___x_673_);
v___x_675_ = lean_array_uset(v_bs_x27_671_, v_i_652_, v___x_672_);
v_i_652_ = v___x_674_;
v_bs_653_ = v___x_675_;
goto _start;
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_v_661_);
lean_dec_ref(v_bs_653_);
lean_dec_ref(v_linter_650_);
v_a_677_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_666_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_666_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object* v_linter_685_, lean_object* v_sz_686_, lean_object* v_i_687_, lean_object* v_bs_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
size_t v_sz_boxed_692_; size_t v_i_boxed_693_; lean_object* v_res_694_; 
v_sz_boxed_692_ = lean_unbox_usize(v_sz_686_);
lean_dec(v_sz_686_);
v_i_boxed_693_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_linter_685_, v_sz_boxed_692_, v_i_boxed_693_, v_bs_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(lean_object* v_decls_695_, size_t v_sz_696_, size_t v_i_697_, lean_object* v_bs_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_697_, v_sz_696_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_bs_698_);
return v___x_703_;
}
else
{
lean_object* v_v_704_; lean_object* v___x_705_; lean_object* v_bs_x27_706_; lean_object* v_a_708_; lean_object* v___y_719_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_v_704_ = lean_array_uget(v_bs_698_, v_i_697_);
v___x_705_ = lean_unsigned_to_nat(0u);
v_bs_x27_706_ = lean_array_uset(v_bs_698_, v_i_697_, v___x_705_);
v___x_729_ = lean_array_get_size(v_decls_695_);
v___x_730_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_731_ = lean_nat_dec_lt(v___x_705_, v___x_729_);
if (v___x_731_ == 0)
{
v_a_708_ = v___x_730_;
goto v___jp_707_;
}
else
{
lean_object* v_name_732_; uint8_t v___x_733_; 
v_name_732_ = lean_ctor_get(v_v_704_, 1);
v___x_733_ = lean_nat_dec_le(v___x_729_, v___x_729_);
if (v___x_733_ == 0)
{
if (v___x_731_ == 0)
{
v_a_708_ = v___x_730_;
goto v___jp_707_;
}
else
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((size_t)0ULL);
v___x_735_ = lean_usize_of_nat(v___x_729_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_732_, v_decls_695_, v___x_734_, v___x_735_, v___x_730_, v___y_699_, v___y_700_);
v___y_719_ = v___x_736_;
goto v___jp_718_;
}
}
else
{
size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((size_t)0ULL);
v___x_738_ = lean_usize_of_nat(v___x_729_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_732_, v_decls_695_, v___x_737_, v___x_738_, v___x_730_, v___y_699_, v___y_700_);
v___y_719_ = v___x_739_;
goto v___jp_718_;
}
}
v___jp_707_:
{
size_t v_sz_709_; size_t v___x_710_; lean_object* v___x_711_; 
v_sz_709_ = lean_array_size(v_a_708_);
v___x_710_ = ((size_t)0ULL);
lean_inc(v_v_704_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_704_, v_sz_709_, v___x_710_, v_a_708_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_v_704_);
lean_ctor_set(v___x_713_, 1, v_a_712_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_697_, v___x_714_);
v___x_716_ = lean_array_uset(v_bs_x27_706_, v_i_697_, v___x_713_);
v_i_697_ = v___x_715_;
v_bs_698_ = v___x_716_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_706_);
lean_dec(v_v_704_);
return v___x_711_;
}
}
v___jp_718_:
{
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v_a_720_; 
v_a_720_ = lean_ctor_get(v___y_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___y_719_);
v_a_708_ = v_a_720_;
goto v___jp_707_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_bs_x27_706_);
lean_dec(v_v_704_);
v_a_721_ = lean_ctor_get(v___y_719_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___y_719_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___y_719_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___y_719_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object* v_decls_740_, lean_object* v_sz_741_, lean_object* v_i_742_, lean_object* v_bs_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
size_t v_sz_boxed_747_; size_t v_i_boxed_748_; lean_object* v_res_749_; 
v_sz_boxed_747_ = lean_unbox_usize(v_sz_741_);
lean_dec(v_sz_741_);
v_i_boxed_748_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_740_, v_sz_boxed_747_, v_i_boxed_748_, v_bs_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v_decls_740_);
return v_res_749_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_750_; uint64_t v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(1723u);
v___x_751_ = lean_uint64_of_nat(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
return v_x_752_;
}
else
{
lean_object* v_key_754_; lean_object* v_value_755_; lean_object* v_tail_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_782_; 
v_key_754_ = lean_ctor_get(v_x_753_, 0);
v_value_755_ = lean_ctor_get(v_x_753_, 1);
v_tail_756_ = lean_ctor_get(v_x_753_, 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_782_ == 0)
{
v___x_758_ = v_x_753_;
v_isShared_759_ = v_isSharedCheck_782_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_tail_756_);
lean_inc(v_value_755_);
lean_inc(v_key_754_);
lean_dec(v_x_753_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_782_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; uint64_t v___y_762_; 
v___x_760_ = lean_array_get_size(v_x_752_);
if (lean_obj_tag(v_key_754_) == 0)
{
uint64_t v___x_780_; 
v___x_780_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_762_ = v___x_780_;
goto v___jp_761_;
}
else
{
uint64_t v_hash_781_; 
v_hash_781_ = lean_ctor_get_uint64(v_key_754_, sizeof(void*)*2);
v___y_762_ = v_hash_781_;
goto v___jp_761_;
}
v___jp_761_:
{
uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v_fold_765_; uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_763_ = 32ULL;
v___x_764_ = lean_uint64_shift_right(v___y_762_, v___x_763_);
v_fold_765_ = lean_uint64_xor(v___y_762_, v___x_764_);
v___x_766_ = 16ULL;
v___x_767_ = lean_uint64_shift_right(v_fold_765_, v___x_766_);
v___x_768_ = lean_uint64_xor(v_fold_765_, v___x_767_);
v___x_769_ = lean_uint64_to_usize(v___x_768_);
v___x_770_ = lean_usize_of_nat(v___x_760_);
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_sub(v___x_770_, v___x_771_);
v___x_773_ = lean_usize_land(v___x_769_, v___x_772_);
v___x_774_ = lean_array_uget_borrowed(v_x_752_, v___x_773_);
lean_inc(v___x_774_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 2, v___x_774_);
v___x_776_ = v___x_758_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_key_754_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_value_755_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v___x_774_);
v___x_776_ = v_reuseFailAlloc_779_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_array_uset(v_x_752_, v___x_773_, v___x_776_);
v_x_752_ = v___x_777_;
v_x_753_ = v_tail_756_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_783_, lean_object* v_source_784_, lean_object* v_target_785_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_array_get_size(v_source_784_);
v___x_787_ = lean_nat_dec_lt(v_i_783_, v___x_786_);
if (v___x_787_ == 0)
{
lean_dec_ref(v_source_784_);
lean_dec(v_i_783_);
return v_target_785_;
}
else
{
lean_object* v_es_788_; lean_object* v___x_789_; lean_object* v_source_790_; lean_object* v_target_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_es_788_ = lean_array_fget(v_source_784_, v_i_783_);
v___x_789_ = lean_box(0);
v_source_790_ = lean_array_fset(v_source_784_, v_i_783_, v___x_789_);
v_target_791_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_target_785_, v_es_788_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_i_783_, v___x_792_);
lean_dec(v_i_783_);
v_i_783_ = v___x_793_;
v_source_784_ = v_source_790_;
v_target_785_ = v_target_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object* v_data_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_nbuckets_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_796_ = lean_array_get_size(v_data_795_);
v___x_797_ = lean_unsigned_to_nat(2u);
v_nbuckets_798_ = lean_nat_mul(v___x_796_, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_box(0);
v___x_801_ = lean_mk_array(v_nbuckets_798_, v___x_800_);
v___x_802_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v___x_799_, v_data_795_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object* v_a_803_, lean_object* v_b_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_dec(v_b_804_);
lean_dec(v_a_803_);
return v_x_805_;
}
else
{
lean_object* v_key_806_; lean_object* v_value_807_; lean_object* v_tail_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_820_; 
v_key_806_ = lean_ctor_get(v_x_805_, 0);
v_value_807_ = lean_ctor_get(v_x_805_, 1);
v_tail_808_ = lean_ctor_get(v_x_805_, 2);
v_isSharedCheck_820_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_820_ == 0)
{
v___x_810_ = v_x_805_;
v_isShared_811_ = v_isSharedCheck_820_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_tail_808_);
lean_inc(v_value_807_);
lean_inc(v_key_806_);
lean_dec(v_x_805_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_820_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = lean_name_eq(v_key_806_, v_a_803_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_803_, v_b_804_, v_tail_808_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 2, v___x_813_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_key_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_value_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_object* v___x_818_; 
lean_dec(v_value_807_);
lean_dec(v_key_806_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_b_804_);
lean_ctor_set(v___x_810_, 0, v_a_803_);
v___x_818_ = v___x_810_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_803_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_b_804_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_tail_808_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
uint8_t v___x_823_; 
v___x_823_ = 0;
return v___x_823_;
}
else
{
lean_object* v_key_824_; lean_object* v_tail_825_; uint8_t v___x_826_; 
v_key_824_ = lean_ctor_get(v_x_822_, 0);
v_tail_825_ = lean_ctor_get(v_x_822_, 2);
v___x_826_ = lean_name_eq(v_key_824_, v_a_821_);
if (v___x_826_ == 0)
{
v_x_822_ = v_tail_825_;
goto _start;
}
else
{
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_828_, lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_828_, v_x_829_);
lean_dec(v_x_829_);
lean_dec(v_a_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object* v_m_832_, lean_object* v_a_833_, lean_object* v_b_834_){
_start:
{
lean_object* v_size_835_; lean_object* v_buckets_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_882_; 
v_size_835_ = lean_ctor_get(v_m_832_, 0);
v_buckets_836_ = lean_ctor_get(v_m_832_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_m_832_);
if (v_isSharedCheck_882_ == 0)
{
v___x_838_ = v_m_832_;
v_isShared_839_ = v_isSharedCheck_882_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_buckets_836_);
lean_inc(v_size_835_);
lean_dec(v_m_832_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_882_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; uint64_t v___y_842_; 
v___x_840_ = lean_array_get_size(v_buckets_836_);
if (lean_obj_tag(v_a_833_) == 0)
{
uint64_t v___x_880_; 
v___x_880_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_842_ = v___x_880_;
goto v___jp_841_;
}
else
{
uint64_t v_hash_881_; 
v_hash_881_ = lean_ctor_get_uint64(v_a_833_, sizeof(void*)*2);
v___y_842_ = v_hash_881_;
goto v___jp_841_;
}
v___jp_841_:
{
uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v_fold_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; lean_object* v_bkt_854_; uint8_t v___x_855_; 
v___x_843_ = 32ULL;
v___x_844_ = lean_uint64_shift_right(v___y_842_, v___x_843_);
v_fold_845_ = lean_uint64_xor(v___y_842_, v___x_844_);
v___x_846_ = 16ULL;
v___x_847_ = lean_uint64_shift_right(v_fold_845_, v___x_846_);
v___x_848_ = lean_uint64_xor(v_fold_845_, v___x_847_);
v___x_849_ = lean_uint64_to_usize(v___x_848_);
v___x_850_ = lean_usize_of_nat(v___x_840_);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_sub(v___x_850_, v___x_851_);
v___x_853_ = lean_usize_land(v___x_849_, v___x_852_);
v_bkt_854_ = lean_array_uget_borrowed(v_buckets_836_, v___x_853_);
v___x_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_833_, v_bkt_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v_size_x27_857_; lean_object* v___x_858_; lean_object* v_buckets_x27_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_856_ = lean_unsigned_to_nat(1u);
v_size_x27_857_ = lean_nat_add(v_size_835_, v___x_856_);
lean_dec(v_size_835_);
lean_inc(v_bkt_854_);
v___x_858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_858_, 0, v_a_833_);
lean_ctor_set(v___x_858_, 1, v_b_834_);
lean_ctor_set(v___x_858_, 2, v_bkt_854_);
v_buckets_x27_859_ = lean_array_uset(v_buckets_836_, v___x_853_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(4u);
v___x_861_ = lean_nat_mul(v_size_x27_857_, v___x_860_);
v___x_862_ = lean_unsigned_to_nat(3u);
v___x_863_ = lean_nat_div(v___x_861_, v___x_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_array_get_size(v_buckets_x27_859_);
v___x_865_ = lean_nat_dec_le(v___x_863_, v___x_864_);
lean_dec(v___x_863_);
if (v___x_865_ == 0)
{
lean_object* v_val_866_; lean_object* v___x_868_; 
v_val_866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_buckets_x27_859_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_val_866_);
lean_ctor_set(v___x_838_, 0, v_size_x27_857_);
v___x_868_ = v___x_838_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_size_x27_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_val_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v___x_871_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_buckets_x27_859_);
lean_ctor_set(v___x_838_, 0, v_size_x27_857_);
v___x_871_ = v___x_838_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_size_x27_857_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_buckets_x27_859_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v___x_873_; lean_object* v_buckets_x27_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
lean_inc(v_bkt_854_);
v___x_873_ = lean_box(0);
v_buckets_x27_874_ = lean_array_uset(v_buckets_836_, v___x_853_, v___x_873_);
v___x_875_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_833_, v_b_834_, v_bkt_854_);
v___x_876_ = lean_array_uset(v_buckets_x27_874_, v___x_853_, v___x_875_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_876_);
v___x_878_ = v___x_838_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_size_835_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object* v_as_886_, size_t v_sz_887_, size_t v_i_888_, lean_object* v_b_889_){
_start:
{
lean_object* v_a_892_; uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_lt(v_i_888_, v_sz_887_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_b_889_);
return v___x_897_;
}
else
{
lean_object* v_a_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_916_; 
v_a_898_ = lean_array_uget(v_as_886_, v_i_888_);
v_fst_899_ = lean_ctor_get(v_a_898_, 0);
v_snd_900_ = lean_ctor_get(v_a_898_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_916_ == 0)
{
v___x_902_ = v_a_898_;
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snd_900_);
lean_inc(v_fst_899_);
lean_dec(v_a_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_val_905_; lean_object* v___x_907_; 
v___x_907_ = lean_task_get_own(v_snd_900_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v___x_909_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1);
v___x_910_ = l_Lean_Exception_toMessageData(v_a_908_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 7);
lean_ctor_set(v___x_902_, 1, v___x_910_);
lean_ctor_set(v___x_902_, 0, v___x_909_);
v___x_912_ = v___x_902_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
v_val_905_ = v___x_912_;
goto v___jp_904_;
}
}
else
{
lean_object* v_a_914_; 
lean_del_object(v___x_902_);
v_a_914_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_907_);
if (lean_obj_tag(v_a_914_) == 1)
{
lean_object* v_val_915_; 
v_val_915_ = lean_ctor_get(v_a_914_, 0);
lean_inc(v_val_915_);
lean_dec_ref(v_a_914_);
v_val_905_ = v_val_915_;
goto v___jp_904_;
}
else
{
lean_dec(v_a_914_);
lean_dec(v_fst_899_);
v_a_892_ = v_b_889_;
goto v___jp_891_;
}
}
v___jp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_889_, v_fst_899_, v_val_905_);
v_a_892_ = v___x_906_;
goto v___jp_891_;
}
}
}
v___jp_891_:
{
size_t v___x_893_; size_t v___x_894_; 
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_add(v_i_888_, v___x_893_);
v_i_888_ = v___x_894_;
v_b_889_ = v_a_892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object* v_as_917_, lean_object* v_sz_918_, lean_object* v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_){
_start:
{
size_t v_sz_boxed_922_; size_t v_i_boxed_923_; lean_object* v_res_924_; 
v_sz_boxed_922_ = lean_unbox_usize(v_sz_918_);
lean_dec(v_sz_918_);
v_i_boxed_923_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_917_, v_sz_boxed_922_, v_i_boxed_923_, v_b_920_);
lean_dec_ref(v_as_917_);
return v_res_924_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_box(0);
v___x_926_ = lean_unsigned_to_nat(16u);
v___x_927_ = lean_mk_array(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(size_t v_sz_931_, size_t v_i_932_, lean_object* v_bs_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_bs_933_);
return v___x_938_;
}
else
{
lean_object* v_v_939_; lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_967_; 
v_v_939_ = lean_array_uget(v_bs_933_, v_i_932_);
v_fst_940_ = lean_ctor_get(v_v_939_, 0);
v_snd_941_ = lean_ctor_get(v_v_939_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_v_939_);
if (v_isSharedCheck_967_ == 0)
{
v___x_943_ = v_v_939_;
v_isShared_944_ = v_isSharedCheck_967_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_940_);
lean_dec(v_v_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_967_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; size_t v_sz_947_; size_t v___x_948_; lean_object* v___x_949_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v_sz_947_ = lean_array_size(v_snd_941_);
v___x_948_ = ((size_t)0ULL);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_snd_941_, v_sz_947_, v___x_948_, v___x_946_);
lean_dec(v_snd_941_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_bs_x27_951_; lean_object* v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_949_);
v_bs_x27_951_ = lean_array_uset(v_bs_933_, v_i_932_, v___x_945_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_a_950_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fst_940_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_a_950_);
v___x_953_ = v_reuseFailAlloc_958_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_932_, v___x_954_);
v___x_956_ = lean_array_uset(v_bs_x27_951_, v_i_932_, v___x_953_);
v_i_932_ = v___x_955_;
v_bs_933_ = v___x_956_;
goto _start;
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_del_object(v___x_943_);
lean_dec(v_fst_940_);
lean_dec_ref(v_bs_933_);
v_a_959_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_949_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_949_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___boxed(lean_object* v_sz_968_, lean_object* v_i_969_, lean_object* v_bs_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_sz_boxed_974_ = lean_unbox_usize(v_sz_968_);
lean_dec(v_sz_968_);
v_i_boxed_975_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_boxed_974_, v_i_boxed_975_, v_bs_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object* v_decls_977_, lean_object* v_linters_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; 
v_sz_982_ = lean_array_size(v_linters_978_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_977_, v_sz_982_, v___x_983_, v_linters_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; size_t v_sz_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v_sz_986_ = lean_array_size(v_a_985_);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_986_, v___x_983_, v_a_985_, v_a_979_, v_a_980_);
return v___x_987_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_984_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_984_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object* v_decls_996_, lean_object* v_linters_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Linter_EnvLinter_lintCore(v_decls_996_, v_linters_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_decls_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object* v_00_u03b2_1002_, lean_object* v_m_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_m_1003_, v_a_1004_, v_b_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object* v_as_1007_, size_t v_sz_1008_, size_t v_i_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_1007_, v_sz_1008_, v_i_1009_, v_b_1010_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object* v_as_1015_, lean_object* v_sz_1016_, lean_object* v_i_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1016_);
lean_dec(v_sz_1016_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(v_as_1015_, v_sz_boxed_1022_, v_i_boxed_1023_, v_b_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_as_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object* v_linter_1025_, lean_object* v_decl_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_1025_, v_decl_1026_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object* v_linter_1031_, lean_object* v_decl_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v_linter_1031_, v_decl_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v_linter_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object* v_00_u03b2_1037_, lean_object* v_a_1038_, lean_object* v_x_1039_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_1038_, v_x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
uint8_t v_res_1044_; lean_object* v_r_1045_; 
v_res_1044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(v_00_u03b2_1041_, v_a_1042_, v_x_1043_);
lean_dec(v_x_1043_);
lean_dec(v_a_1042_);
v_r_1045_ = lean_box(v_res_1044_);
return v_r_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object* v_00_u03b2_1046_, lean_object* v_data_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_data_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object* v_00_u03b2_1049_, lean_object* v_a_1050_, lean_object* v_b_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_1050_, v_b_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1054_, lean_object* v_i_1055_, lean_object* v_source_1056_, lean_object* v_target_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v_i_1055_, v_source_1056_, v_target_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_x_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object* v_a_1063_, lean_object* v_fallback_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_inc(v_fallback_1064_);
return v_fallback_1064_;
}
else
{
lean_object* v_key_1066_; lean_object* v_value_1067_; lean_object* v_tail_1068_; uint8_t v___x_1069_; 
v_key_1066_ = lean_ctor_get(v_x_1065_, 0);
v_value_1067_ = lean_ctor_get(v_x_1065_, 1);
v_tail_1068_ = lean_ctor_get(v_x_1065_, 2);
v___x_1069_ = lean_name_eq(v_key_1066_, v_a_1063_);
if (v___x_1069_ == 0)
{
v_x_1065_ = v_tail_1068_;
goto _start;
}
else
{
lean_inc(v_value_1067_);
return v_value_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object* v_a_1071_, lean_object* v_fallback_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1071_, v_fallback_1072_, v_x_1073_);
lean_dec(v_x_1073_);
lean_dec(v_fallback_1072_);
lean_dec(v_a_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object* v_m_1075_, lean_object* v_a_1076_, lean_object* v_fallback_1077_){
_start:
{
lean_object* v_buckets_1078_; lean_object* v___x_1079_; uint64_t v___y_1081_; 
v_buckets_1078_ = lean_ctor_get(v_m_1075_, 1);
v___x_1079_ = lean_array_get_size(v_buckets_1078_);
if (lean_obj_tag(v_a_1076_) == 0)
{
uint64_t v___x_1095_; 
v___x_1095_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_1081_ = v___x_1095_;
goto v___jp_1080_;
}
else
{
uint64_t v_hash_1096_; 
v_hash_1096_ = lean_ctor_get_uint64(v_a_1076_, sizeof(void*)*2);
v___y_1081_ = v_hash_1096_;
goto v___jp_1080_;
}
v___jp_1080_:
{
uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v_fold_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1082_ = 32ULL;
v___x_1083_ = lean_uint64_shift_right(v___y_1081_, v___x_1082_);
v_fold_1084_ = lean_uint64_xor(v___y_1081_, v___x_1083_);
v___x_1085_ = 16ULL;
v___x_1086_ = lean_uint64_shift_right(v_fold_1084_, v___x_1085_);
v___x_1087_ = lean_uint64_xor(v_fold_1084_, v___x_1086_);
v___x_1088_ = lean_uint64_to_usize(v___x_1087_);
v___x_1089_ = lean_usize_of_nat(v___x_1079_);
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_sub(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_usize_land(v___x_1088_, v___x_1091_);
v___x_1093_ = lean_array_uget_borrowed(v_buckets_1078_, v___x_1092_);
v___x_1094_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1076_, v_fallback_1077_, v___x_1093_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object* v_m_1097_, lean_object* v_a_1098_, lean_object* v_fallback_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1097_, v_a_1098_, v_fallback_1099_);
lean_dec(v_fallback_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_m_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object* v_a_1101_, lean_object* v_hi_1102_, lean_object* v_pivot_1103_, lean_object* v_as_1104_, lean_object* v_i_1105_, lean_object* v_k_1106_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_nat_dec_lt(v_k_1106_, v_hi_1102_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec(v_k_1106_);
v___x_1108_ = lean_array_fswap(v_as_1104_, v_i_1105_, v_hi_1102_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_i_1105_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; lean_object* v_fst_1111_; lean_object* v_fst_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1110_ = lean_array_fget_borrowed(v_as_1104_, v_k_1106_);
v_fst_1111_ = lean_ctor_get(v___x_1110_, 0);
v_fst_1112_ = lean_ctor_get(v_pivot_1103_, 0);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1101_, v_fst_1111_, v___x_1113_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1101_, v_fst_1112_, v___x_1113_);
v___x_1116_ = lean_nat_dec_lt(v___x_1114_, v___x_1115_);
lean_dec(v___x_1115_);
lean_dec(v___x_1114_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_k_1106_, v___x_1117_);
lean_dec(v_k_1106_);
v_k_1106_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = lean_array_fswap(v_as_1104_, v_i_1105_, v_k_1106_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_i_1105_, v___x_1121_);
lean_dec(v_i_1105_);
v___x_1123_ = lean_nat_add(v_k_1106_, v___x_1121_);
lean_dec(v_k_1106_);
v_as_1104_ = v___x_1120_;
v_i_1105_ = v___x_1122_;
v_k_1106_ = v___x_1123_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object* v_a_1125_, lean_object* v_hi_1126_, lean_object* v_pivot_1127_, lean_object* v_as_1128_, lean_object* v_i_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1125_, v_hi_1126_, v_pivot_1127_, v_as_1128_, v_i_1129_, v_k_1130_);
lean_dec_ref(v_pivot_1127_);
lean_dec(v_hi_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object* v_a_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_fst_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_fst_1135_ = lean_ctor_get(v_x_1133_, 0);
v_fst_1136_ = lean_ctor_get(v_x_1134_, 0);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1132_, v_fst_1135_, v___x_1137_);
v___x_1139_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1132_, v_fst_1136_, v___x_1137_);
v___x_1140_ = lean_nat_dec_lt(v___x_1138_, v___x_1139_);
lean_dec(v___x_1139_);
lean_dec(v___x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object* v_a_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1141_, v_x_1142_, v_x_1143_);
lean_dec_ref(v_x_1143_);
lean_dec_ref(v_x_1142_);
lean_dec_ref(v_a_1141_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object* v_a_1146_, lean_object* v_n_1147_, lean_object* v_as_1148_, lean_object* v_lo_1149_, lean_object* v_hi_1150_){
_start:
{
lean_object* v___y_1152_; uint8_t v___x_1162_; 
v___x_1162_ = lean_nat_dec_lt(v_lo_1149_, v_hi_1150_);
if (v___x_1162_ == 0)
{
lean_dec(v_lo_1149_);
return v_as_1148_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_mid_1165_; lean_object* v___y_1167_; lean_object* v___y_1173_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1163_ = lean_nat_add(v_lo_1149_, v_hi_1150_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v_mid_1165_ = lean_nat_shiftr(v___x_1163_, v___x_1164_);
lean_dec(v___x_1163_);
v___x_1178_ = lean_array_fget_borrowed(v_as_1148_, v_mid_1165_);
v___x_1179_ = lean_array_fget_borrowed(v_as_1148_, v_lo_1149_);
v___x_1180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1146_, v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
v___y_1173_ = v_as_1148_;
goto v___jp_1172_;
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_array_fswap(v_as_1148_, v_lo_1149_, v_mid_1165_);
v___y_1173_ = v___x_1181_;
goto v___jp_1172_;
}
v___jp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_array_fget_borrowed(v___y_1167_, v_mid_1165_);
v___x_1169_ = lean_array_fget_borrowed(v___y_1167_, v_hi_1150_);
v___x_1170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1146_, v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_dec(v_mid_1165_);
v___y_1152_ = v___y_1167_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_array_fswap(v___y_1167_, v_mid_1165_, v_hi_1150_);
lean_dec(v_mid_1165_);
v___y_1152_ = v___x_1171_;
goto v___jp_1151_;
}
}
v___jp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_array_fget_borrowed(v___y_1173_, v_hi_1150_);
v___x_1175_ = lean_array_fget_borrowed(v___y_1173_, v_lo_1149_);
v___x_1176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1146_, v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
v___y_1167_ = v___y_1173_;
goto v___jp_1166_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_array_fswap(v___y_1173_, v_lo_1149_, v_hi_1150_);
v___y_1167_ = v___x_1177_;
goto v___jp_1166_;
}
}
}
v___jp_1151_:
{
lean_object* v_pivot_1153_; lean_object* v___x_1154_; lean_object* v_fst_1155_; lean_object* v_snd_1156_; uint8_t v___x_1157_; 
v_pivot_1153_ = lean_array_fget(v___y_1152_, v_hi_1150_);
lean_inc_n(v_lo_1149_, 2);
v___x_1154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1146_, v_hi_1150_, v_pivot_1153_, v___y_1152_, v_lo_1149_, v_lo_1149_);
lean_dec(v_pivot_1153_);
v_fst_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_fst_1155_);
v_snd_1156_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_snd_1156_);
lean_dec_ref(v___x_1154_);
v___x_1157_ = lean_nat_dec_le(v_hi_1150_, v_fst_1155_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1146_, v_n_1147_, v_snd_1156_, v_lo_1149_, v_fst_1155_);
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_add(v_fst_1155_, v___x_1159_);
lean_dec(v_fst_1155_);
v_as_1148_ = v___x_1158_;
v_lo_1149_ = v___x_1160_;
goto _start;
}
else
{
lean_dec(v_fst_1155_);
lean_dec(v_lo_1149_);
return v_snd_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object* v_a_1182_, lean_object* v_n_1183_, lean_object* v_as_1184_, lean_object* v_lo_1185_, lean_object* v_hi_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1182_, v_n_1183_, v_as_1184_, v_lo_1185_, v_hi_1186_);
lean_dec(v_hi_1186_);
lean_dec(v_n_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object* v_declName_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1191_ = lean_st_ref_get(v___y_1189_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = l_Lean_isRecCore(v_env_1192_, v_declName_1188_);
v___x_1194_ = lean_box(v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1196_, v___y_1197_);
lean_dec(v___y_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object* v_declName_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v_env_1204_; lean_object* v___x_1205_; lean_object* v_env_1206_; lean_object* v___x_1207_; lean_object* v_toEnvExtension_1208_; lean_object* v_asyncMode_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1203_ = lean_st_ref_get(v___y_1201_);
v_env_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc_ref(v_env_1204_);
lean_dec(v___x_1203_);
v___x_1205_ = lean_st_ref_get(v___y_1201_);
v_env_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_ref(v_env_1206_);
lean_dec(v___x_1205_);
v___x_1207_ = l_Lean_declRangeExt;
v_toEnvExtension_1208_ = lean_ctor_get(v___x_1207_, 0);
v_asyncMode_1209_ = lean_ctor_get(v_toEnvExtension_1208_, 2);
v___x_1210_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1211_ = 0;
lean_inc(v_declName_1200_);
v___x_1212_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1210_, v___x_1207_, v_env_1204_, v_declName_1200_, v_asyncMode_1209_, v___x_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = 1;
v___x_1214_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1210_, v___x_1207_, v_env_1206_, v_declName_1200_, v_asyncMode_1209_, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; 
lean_dec_ref(v_env_1206_);
lean_dec(v_declName_1200_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1212_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1217_, v___y_1218_);
lean_dec(v___y_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object* v_declName_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_ranges_1226_; lean_object* v___x_1232_; lean_object* v_env_1233_; lean_object* v___x_1234_; lean_object* v_a_1235_; uint8_t v___y_1241_; uint8_t v___x_1245_; 
v___x_1232_ = lean_st_ref_get(v___y_1223_);
v_env_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref_n(v_env_1233_, 2);
lean_dec(v___x_1232_);
lean_inc_n(v_declName_1221_, 2);
v___x_1234_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1221_, v___y_1223_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
v___x_1245_ = l_Lean_isAuxRecursor(v_env_1233_, v_declName_1221_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
lean_inc(v_declName_1221_);
v___x_1246_ = l_Lean_isNoConfusion(v_env_1233_, v_declName_1221_);
v___y_1241_ = v___x_1246_;
goto v___jp_1240_;
}
else
{
lean_dec_ref(v_env_1233_);
v___y_1241_ = v___x_1245_;
goto v___jp_1240_;
}
v___jp_1225_:
{
if (lean_obj_tag(v_ranges_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = l_Lean_builtinDeclRanges;
v___x_1228_ = lean_st_ref_get(v___x_1227_);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1228_, v_declName_1221_);
lean_dec(v_declName_1221_);
lean_dec(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_declName_1221_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_ranges_1226_);
return v___x_1231_;
}
}
v___jp_1236_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; 
v___x_1237_ = l_Lean_Name_getPrefix(v_declName_1221_);
v___x_1238_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v___x_1237_, v___y_1223_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v_ranges_1226_ = v_a_1239_;
goto v___jp_1225_;
}
v___jp_1240_:
{
if (v___y_1241_ == 0)
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v_a_1244_; 
lean_inc(v_declName_1221_);
v___x_1243_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1221_, v___y_1223_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v_ranges_1226_ = v_a_1244_;
goto v___jp_1225_;
}
else
{
goto v___jp_1236_;
}
}
else
{
lean_dec(v_a_1235_);
goto v___jp_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object* v_declName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object* v_as_1252_, size_t v_sz_1253_, size_t v_i_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_usize_dec_lt(v_i_1254_, v_sz_1253_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_b_1255_);
return v___x_1260_;
}
else
{
lean_object* v_a_1261_; lean_object* v_fst_1262_; lean_object* v___x_1263_; 
v_a_1261_ = lean_array_uget_borrowed(v_as_1252_, v_i_1254_);
v_fst_1262_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_fst_1262_);
v___x_1263_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_fst_1262_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_a_1266_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
if (lean_obj_tag(v_a_1264_) == 1)
{
lean_object* v_val_1270_; lean_object* v_range_1271_; lean_object* v_pos_1272_; lean_object* v_line_1273_; lean_object* v___x_1274_; 
v_val_1270_ = lean_ctor_get(v_a_1264_, 0);
lean_inc(v_val_1270_);
lean_dec_ref(v_a_1264_);
v_range_1271_ = lean_ctor_get(v_val_1270_, 0);
lean_inc_ref(v_range_1271_);
lean_dec(v_val_1270_);
v_pos_1272_ = lean_ctor_get(v_range_1271_, 0);
lean_inc_ref(v_pos_1272_);
lean_dec_ref(v_range_1271_);
v_line_1273_ = lean_ctor_get(v_pos_1272_, 0);
lean_inc(v_line_1273_);
lean_dec_ref(v_pos_1272_);
lean_inc(v_fst_1262_);
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_1255_, v_fst_1262_, v_line_1273_);
v_a_1266_ = v___x_1274_;
goto v___jp_1265_;
}
else
{
lean_dec(v_a_1264_);
v_a_1266_ = v_b_1255_;
goto v___jp_1265_;
}
v___jp_1265_:
{
size_t v___x_1267_; size_t v___x_1268_; 
v___x_1267_ = ((size_t)1ULL);
v___x_1268_ = lean_usize_add(v_i_1254_, v___x_1267_);
v_i_1254_ = v___x_1268_;
v_b_1255_ = v_a_1266_;
goto _start;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v_b_1255_);
v_a_1275_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1263_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1263_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object* v_as_1283_, lean_object* v_sz_1284_, lean_object* v_i_1285_, lean_object* v_b_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
size_t v_sz_boxed_1290_; size_t v_i_boxed_1291_; lean_object* v_res_1292_; 
v_sz_boxed_1290_ = lean_unbox_usize(v_sz_1284_);
lean_dec(v_sz_1284_);
v_i_boxed_1291_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_res_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1283_, v_sz_boxed_1290_, v_i_boxed_1291_, v_b_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_as_1283_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 0)
{
return v_x_1293_;
}
else
{
lean_object* v_key_1295_; lean_object* v_value_1296_; lean_object* v_tail_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_key_1295_ = lean_ctor_get(v_x_1294_, 0);
v_value_1296_ = lean_ctor_get(v_x_1294_, 1);
v_tail_1297_ = lean_ctor_get(v_x_1294_, 2);
lean_inc(v_value_1296_);
lean_inc(v_key_1295_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_key_1295_);
lean_ctor_set(v___x_1298_, 1, v_value_1296_);
v___x_1299_ = lean_array_push(v_x_1293_, v___x_1298_);
v_x_1293_ = v___x_1299_;
v_x_1294_ = v_tail_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1301_, v_x_1302_);
lean_dec(v_x_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object* v_as_1304_, size_t v_i_1305_, size_t v_stop_1306_, lean_object* v_b_1307_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_eq(v_i_1305_, v_stop_1306_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; 
v___x_1309_ = lean_array_uget_borrowed(v_as_1304_, v_i_1305_);
v___x_1310_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_b_1307_, v___x_1309_);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1305_, v___x_1311_);
v_i_1305_ = v___x_1312_;
v_b_1307_ = v___x_1310_;
goto _start;
}
else
{
return v_b_1307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object* v_as_1314_, lean_object* v_i_1315_, lean_object* v_stop_1316_, lean_object* v_b_1317_){
_start:
{
size_t v_i_boxed_1318_; size_t v_stop_boxed_1319_; lean_object* v_res_1320_; 
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_stop_boxed_1319_ = lean_unbox_usize(v_stop_1316_);
lean_dec(v_stop_1316_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1314_, v_i_boxed_1318_, v_stop_boxed_1319_, v_b_1317_);
lean_dec_ref(v_as_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object* v_results_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v_size_1340_; lean_object* v_buckets_1341_; lean_object* v___x_1342_; lean_object* v_key_1343_; lean_object* v___y_1345_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_size_1340_ = lean_ctor_get(v_results_1321_, 0);
v_buckets_1341_ = lean_ctor_get(v_results_1321_, 1);
v___x_1342_ = lean_unsigned_to_nat(0u);
v_key_1343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_1370_ = lean_mk_empty_array_with_capacity(v_size_1340_);
v___x_1371_ = lean_array_get_size(v_buckets_1341_);
v___x_1372_ = lean_nat_dec_lt(v___x_1342_, v___x_1371_);
if (v___x_1372_ == 0)
{
v___y_1345_ = v___x_1370_;
goto v___jp_1344_;
}
else
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_nat_dec_le(v___x_1371_, v___x_1371_);
if (v___x_1373_ == 0)
{
if (v___x_1372_ == 0)
{
v___y_1345_ = v___x_1370_;
goto v___jp_1344_;
}
else
{
size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = ((size_t)0ULL);
v___x_1375_ = lean_usize_of_nat(v___x_1371_);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1341_, v___x_1374_, v___x_1375_, v___x_1370_);
v___y_1345_ = v___x_1376_;
goto v___jp_1344_;
}
}
else
{
size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_of_nat(v___x_1371_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1341_, v___x_1377_, v___x_1378_, v___x_1370_);
v___y_1345_ = v___x_1379_;
goto v___jp_1344_;
}
}
v___jp_1325_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v___y_1326_, v___y_1328_, v___y_1327_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1326_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
v___jp_1333_:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_nat_dec_le(v___y_1338_, v___y_1334_);
if (v___x_1339_ == 0)
{
lean_dec(v___y_1334_);
lean_inc(v___y_1338_);
v___y_1326_ = v___y_1335_;
v___y_1327_ = v___y_1336_;
v___y_1328_ = v___y_1337_;
v___y_1329_ = v___y_1338_;
v___y_1330_ = v___y_1338_;
goto v___jp_1325_;
}
else
{
v___y_1326_ = v___y_1335_;
v___y_1327_ = v___y_1336_;
v___y_1328_ = v___y_1337_;
v___y_1329_ = v___y_1338_;
v___y_1330_ = v___y_1334_;
goto v___jp_1325_;
}
}
v___jp_1344_:
{
size_t v_sz_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_sz_1346_ = lean_array_size(v___y_1345_);
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v___y_1345_, v_sz_1346_, v___x_1347_, v_key_1343_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1361_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1361_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1361_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = lean_array_get_size(v___y_1345_);
v___x_1354_ = lean_nat_dec_eq(v___x_1353_, v___x_1342_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
lean_del_object(v___x_1351_);
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_sub(v___x_1353_, v___x_1355_);
v___x_1357_ = lean_nat_dec_le(v___x_1342_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_inc(v___x_1356_);
v___y_1334_ = v___x_1356_;
v___y_1335_ = v_a_1349_;
v___y_1336_ = v___y_1345_;
v___y_1337_ = v___x_1353_;
v___y_1338_ = v___x_1356_;
goto v___jp_1333_;
}
else
{
v___y_1334_ = v___x_1356_;
v___y_1335_ = v_a_1349_;
v___y_1336_ = v___y_1345_;
v___y_1337_ = v___x_1353_;
v___y_1338_ = v___x_1342_;
goto v___jp_1333_;
}
}
else
{
lean_object* v___x_1359_; 
lean_dec(v_a_1349_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___y_1345_);
v___x_1359_ = v___x_1351_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___y_1345_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v___y_1345_);
v_a_1362_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1348_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1348_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object* v_results_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec_ref(v_results_1380_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object* v_00_u03b1_1385_, lean_object* v_results_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1386_, v_a_1387_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_results_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Linter_EnvLinter_sortResults(v_00_u03b1_1391_, v_results_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec_ref(v_results_1392_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object* v_declName_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1397_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object* v_declName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(v_declName_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object* v_declName_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1407_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object* v_declName_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(v_declName_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object* v_00_u03b1_1417_, lean_object* v_as_1418_, size_t v_sz_1419_, size_t v_i_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1418_, v_sz_1419_, v_i_1420_, v_b_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_as_1427_, lean_object* v_sz_1428_, lean_object* v_i_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
size_t v_sz_boxed_1434_; size_t v_i_boxed_1435_; lean_object* v_res_1436_; 
v_sz_boxed_1434_ = lean_unbox_usize(v_sz_1428_);
lean_dec(v_sz_1428_);
v_i_boxed_1435_ = lean_unbox_usize(v_i_1429_);
lean_dec(v_i_1429_);
v_res_1436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(v_00_u03b1_1426_, v_as_1427_, v_sz_boxed_1434_, v_i_boxed_1435_, v_b_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_as_1427_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object* v_00_u03b2_1437_, lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_fallback_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1438_, v_a_1439_, v_fallback_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object* v_00_u03b2_1442_, lean_object* v_m_1443_, lean_object* v_a_1444_, lean_object* v_fallback_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(v_00_u03b2_1442_, v_m_1443_, v_a_1444_, v_fallback_1445_);
lean_dec(v_fallback_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_m_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object* v_00_u03b1_1447_, lean_object* v_a_1448_, lean_object* v_n_1449_, lean_object* v_as_1450_, lean_object* v_lo_1451_, lean_object* v_hi_1452_, lean_object* v_w_1453_, lean_object* v_hlo_1454_, lean_object* v_hhi_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1448_, v_n_1449_, v_as_1450_, v_lo_1451_, v_hi_1452_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object* v_00_u03b1_1457_, lean_object* v_a_1458_, lean_object* v_n_1459_, lean_object* v_as_1460_, lean_object* v_lo_1461_, lean_object* v_hi_1462_, lean_object* v_w_1463_, lean_object* v_hlo_1464_, lean_object* v_hhi_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(v_00_u03b1_1457_, v_a_1458_, v_n_1459_, v_as_1460_, v_lo_1461_, v_hi_1462_, v_w_1463_, v_hlo_1464_, v_hhi_1465_);
lean_dec(v_hi_1462_);
lean_dec(v_n_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object* v_00_u03b1_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1468_, v_x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(v_00_u03b1_1471_, v_x_1472_, v_x_1473_);
lean_dec(v_x_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object* v_00_u03b1_1475_, lean_object* v_as_1476_, size_t v_i_1477_, size_t v_stop_1478_, lean_object* v_b_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1476_, v_i_1477_, v_stop_1478_, v_b_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_as_1482_, lean_object* v_i_1483_, lean_object* v_stop_1484_, lean_object* v_b_1485_){
_start:
{
size_t v_i_boxed_1486_; size_t v_stop_boxed_1487_; lean_object* v_res_1488_; 
v_i_boxed_1486_ = lean_unbox_usize(v_i_1483_);
lean_dec(v_i_1483_);
v_stop_boxed_1487_ = lean_unbox_usize(v_stop_1484_);
lean_dec(v_stop_1484_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(v_00_u03b1_1481_, v_as_1482_, v_i_boxed_1486_, v_stop_boxed_1487_, v_b_1485_);
lean_dec_ref(v_as_1482_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object* v_00_u03b2_1489_, lean_object* v_a_1490_, lean_object* v_fallback_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1490_, v_fallback_1491_, v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1494_, lean_object* v_a_1495_, lean_object* v_fallback_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(v_00_u03b2_1494_, v_a_1495_, v_fallback_1496_, v_x_1497_);
lean_dec(v_x_1497_);
lean_dec(v_fallback_1496_);
lean_dec(v_a_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object* v_00_u03b1_1499_, lean_object* v_a_1500_, lean_object* v_n_1501_, lean_object* v_lo_1502_, lean_object* v_hi_1503_, lean_object* v_hhi_1504_, lean_object* v_pivot_1505_, lean_object* v_as_1506_, lean_object* v_i_1507_, lean_object* v_k_1508_, lean_object* v_ilo_1509_, lean_object* v_ik_1510_, lean_object* v_w_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1500_, v_hi_1503_, v_pivot_1505_, v_as_1506_, v_i_1507_, v_k_1508_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_a_1514_, lean_object* v_n_1515_, lean_object* v_lo_1516_, lean_object* v_hi_1517_, lean_object* v_hhi_1518_, lean_object* v_pivot_1519_, lean_object* v_as_1520_, lean_object* v_i_1521_, lean_object* v_k_1522_, lean_object* v_ilo_1523_, lean_object* v_ik_1524_, lean_object* v_w_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(v_00_u03b1_1513_, v_a_1514_, v_n_1515_, v_lo_1516_, v_hi_1517_, v_hhi_1518_, v_pivot_1519_, v_as_1520_, v_i_1521_, v_k_1522_, v_ilo_1523_, v_ik_1524_, v_w_1525_);
lean_dec_ref(v_pivot_1519_);
lean_dec(v_hi_1517_);
lean_dec(v_lo_1516_);
lean_dec(v_n_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1526_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
lean_ctor_set(v___x_1529_, 2, v___x_1528_);
lean_ctor_set(v___x_1529_, 3, v___x_1528_);
lean_ctor_set(v___x_1529_, 4, v___x_1527_);
lean_ctor_set(v___x_1529_, 5, v___x_1527_);
lean_ctor_set(v___x_1529_, 6, v___x_1527_);
lean_ctor_set(v___x_1529_, 7, v___x_1527_);
lean_ctor_set(v___x_1529_, 8, v___x_1527_);
lean_ctor_set(v___x_1529_, 9, v___x_1527_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_unsigned_to_nat(32u);
v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1530_);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2(void){
_start:
{
size_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1533_ = ((size_t)5ULL);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_unsigned_to_nat(32u);
v___x_1536_ = lean_mk_empty_array_with_capacity(v___x_1535_);
v___x_1537_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1);
v___x_1538_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
lean_ctor_set(v___x_1538_, 2, v___x_1534_);
lean_ctor_set(v___x_1538_, 3, v___x_1534_);
lean_ctor_set_usize(v___x_1538_, 4, v___x_1533_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_box(1);
v___x_1540_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2);
v___x_1541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1540_);
lean_ctor_set(v___x_1542_, 2, v___x_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object* v_msgData_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v_env_1548_; lean_object* v_options_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1547_ = lean_st_ref_get(v___y_1545_);
v_env_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc_ref(v_env_1548_);
lean_dec(v___x_1547_);
v_options_1549_ = lean_ctor_get(v___y_1544_, 2);
v___x_1550_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1551_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
lean_inc_ref(v_options_1549_);
v___x_1552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1552_, 0, v_env_1548_);
lean_ctor_set(v___x_1552_, 1, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v___x_1551_);
lean_ctor_set(v___x_1552_, 3, v_options_1549_);
v___x_1553_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v_msgData_1543_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object* v_msgData_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msgData_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
if (lean_obj_tag(v_a_1560_) == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = l_List_reverse___redArg(v_a_1561_);
return v___x_1562_;
}
else
{
lean_object* v_head_1563_; lean_object* v_tail_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1573_; 
v_head_1563_ = lean_ctor_get(v_a_1560_, 0);
v_tail_1564_ = lean_ctor_get(v_a_1560_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1566_ = v_a_1560_;
v_isShared_1567_ = v_isSharedCheck_1573_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_tail_1564_);
lean_inc(v_head_1563_);
lean_dec(v_a_1560_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1573_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = l_Lean_mkLevelParam(v_head_1563_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v_a_1561_);
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_a_1561_);
v___x_1570_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
v_a_1560_ = v_tail_1564_;
v_a_1561_ = v___x_1570_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_ref_1578_; lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1588_; 
v_ref_1578_ = lean_ctor_get(v___y_1575_, 5);
v___x_1579_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msg_1574_, v___y_1575_, v___y_1576_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_inc(v_ref_1578_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_ref_1578_);
lean_ctor_set(v___x_1584_, 1, v_a_1580_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1584_);
v___x_1586_ = v___x_1582_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_1594_, lean_object* v_msg_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_fileName_1599_; lean_object* v_fileMap_1600_; lean_object* v_options_1601_; lean_object* v_currRecDepth_1602_; lean_object* v_maxRecDepth_1603_; lean_object* v_ref_1604_; lean_object* v_currNamespace_1605_; lean_object* v_openDecls_1606_; lean_object* v_initHeartbeats_1607_; lean_object* v_maxHeartbeats_1608_; lean_object* v_quotContext_1609_; lean_object* v_currMacroScope_1610_; uint8_t v_diag_1611_; lean_object* v_cancelTk_x3f_1612_; uint8_t v_suppressElabErrors_1613_; lean_object* v_inheritedTraceOptions_1614_; lean_object* v_ref_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_fileName_1599_ = lean_ctor_get(v___y_1596_, 0);
v_fileMap_1600_ = lean_ctor_get(v___y_1596_, 1);
v_options_1601_ = lean_ctor_get(v___y_1596_, 2);
v_currRecDepth_1602_ = lean_ctor_get(v___y_1596_, 3);
v_maxRecDepth_1603_ = lean_ctor_get(v___y_1596_, 4);
v_ref_1604_ = lean_ctor_get(v___y_1596_, 5);
v_currNamespace_1605_ = lean_ctor_get(v___y_1596_, 6);
v_openDecls_1606_ = lean_ctor_get(v___y_1596_, 7);
v_initHeartbeats_1607_ = lean_ctor_get(v___y_1596_, 8);
v_maxHeartbeats_1608_ = lean_ctor_get(v___y_1596_, 9);
v_quotContext_1609_ = lean_ctor_get(v___y_1596_, 10);
v_currMacroScope_1610_ = lean_ctor_get(v___y_1596_, 11);
v_diag_1611_ = lean_ctor_get_uint8(v___y_1596_, sizeof(void*)*14);
v_cancelTk_x3f_1612_ = lean_ctor_get(v___y_1596_, 12);
v_suppressElabErrors_1613_ = lean_ctor_get_uint8(v___y_1596_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1614_ = lean_ctor_get(v___y_1596_, 13);
v_ref_1615_ = l_Lean_replaceRef(v_ref_1594_, v_ref_1604_);
lean_inc_ref(v_inheritedTraceOptions_1614_);
lean_inc(v_cancelTk_x3f_1612_);
lean_inc(v_currMacroScope_1610_);
lean_inc(v_quotContext_1609_);
lean_inc(v_maxHeartbeats_1608_);
lean_inc(v_initHeartbeats_1607_);
lean_inc(v_openDecls_1606_);
lean_inc(v_currNamespace_1605_);
lean_inc(v_maxRecDepth_1603_);
lean_inc(v_currRecDepth_1602_);
lean_inc_ref(v_options_1601_);
lean_inc_ref(v_fileMap_1600_);
lean_inc_ref(v_fileName_1599_);
v___x_1616_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1616_, 0, v_fileName_1599_);
lean_ctor_set(v___x_1616_, 1, v_fileMap_1600_);
lean_ctor_set(v___x_1616_, 2, v_options_1601_);
lean_ctor_set(v___x_1616_, 3, v_currRecDepth_1602_);
lean_ctor_set(v___x_1616_, 4, v_maxRecDepth_1603_);
lean_ctor_set(v___x_1616_, 5, v_ref_1615_);
lean_ctor_set(v___x_1616_, 6, v_currNamespace_1605_);
lean_ctor_set(v___x_1616_, 7, v_openDecls_1606_);
lean_ctor_set(v___x_1616_, 8, v_initHeartbeats_1607_);
lean_ctor_set(v___x_1616_, 9, v_maxHeartbeats_1608_);
lean_ctor_set(v___x_1616_, 10, v_quotContext_1609_);
lean_ctor_set(v___x_1616_, 11, v_currMacroScope_1610_);
lean_ctor_set(v___x_1616_, 12, v_cancelTk_x3f_1612_);
lean_ctor_set(v___x_1616_, 13, v_inheritedTraceOptions_1614_);
lean_ctor_set_uint8(v___x_1616_, sizeof(void*)*14, v_diag_1611_);
lean_ctor_set_uint8(v___x_1616_, sizeof(void*)*14 + 1, v_suppressElabErrors_1613_);
v___x_1617_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1595_, v___x_1616_, v___y_1597_);
lean_dec_ref(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1618_, lean_object* v_msg_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1618_, v_msg_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v_ref_1618_);
return v_res_1623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1645_, lean_object* v_declHint_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v_env_1650_; uint8_t v___x_1651_; 
v___x_1649_ = lean_st_ref_get(v___y_1647_);
v_env_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc_ref(v_env_1650_);
lean_dec(v___x_1649_);
v___x_1651_ = l_Lean_Name_isAnonymous(v_declHint_1646_);
if (v___x_1651_ == 0)
{
uint8_t v_isExporting_1652_; 
v_isExporting_1652_ = lean_ctor_get_uint8(v_env_1650_, sizeof(void*)*8);
if (v_isExporting_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v_env_1650_);
lean_dec(v_declHint_1646_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_msg_1645_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
lean_inc_ref(v_env_1650_);
v___x_1654_ = l_Lean_Environment_setExporting(v_env_1650_, v___x_1651_);
lean_inc(v_declHint_1646_);
lean_inc_ref(v___x_1654_);
v___x_1655_ = l_Lean_Environment_contains(v___x_1654_, v_declHint_1646_, v_isExporting_1652_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec_ref(v___x_1654_);
lean_dec_ref(v_env_1650_);
lean_dec(v_declHint_1646_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_msg_1645_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_c_1662_; lean_object* v___x_1663_; 
v___x_1657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1658_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
v___x_1659_ = l_Lean_Options_empty;
v___x_1660_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1654_);
lean_ctor_set(v___x_1660_, 1, v___x_1657_);
lean_ctor_set(v___x_1660_, 2, v___x_1658_);
lean_ctor_set(v___x_1660_, 3, v___x_1659_);
lean_inc(v_declHint_1646_);
v___x_1661_ = l_Lean_MessageData_ofConstName(v_declHint_1646_, v___x_1651_);
v_c_1662_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1662_, 0, v___x_1660_);
lean_ctor_set(v_c_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1650_, v_declHint_1646_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v_env_1650_);
lean_dec(v_declHint_1646_);
v___x_1664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_c_1662_);
v___x_1666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_MessageData_note(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_msg_1645_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
else
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1706_; 
v_val_1671_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1673_ = v___x_1663_;
v_isShared_1674_ = v_isSharedCheck_1706_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v___x_1663_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1706_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v_mod_1678_; uint8_t v___x_1679_; 
v___x_1675_ = lean_box(0);
v___x_1676_ = l_Lean_Environment_header(v_env_1650_);
lean_dec_ref(v_env_1650_);
v___x_1677_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1676_);
v_mod_1678_ = lean_array_get(v___x_1675_, v___x_1677_, v_val_1671_);
lean_dec(v_val_1671_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = l_Lean_isPrivateName(v_declHint_1646_);
lean_dec(v_declHint_1646_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v_c_1662_);
v___x_1682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_MessageData_ofName(v_mod_1678_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_MessageData_note(v___x_1687_);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_msg_1645_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1689_);
v___x_1691_ = v___x_1673_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_c_1662_);
v___x_1695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_MessageData_ofName(v_mod_1678_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_MessageData_note(v___x_1700_);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_msg_1645_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1702_);
v___x_1704_ = v___x_1673_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref(v_env_1650_);
lean_dec(v_declHint_1646_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_msg_1645_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1708_, lean_object* v_declHint_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1708_, v_declHint_1709_, v___y_1710_);
lean_dec(v___y_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_1713_, lean_object* v_declHint_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1728_; 
v___x_1718_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1713_, v_declHint_1714_, v___y_1716_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1723_ = l_Lean_unknownIdentifierMessageTag;
v___x_1724_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v_a_1719_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1724_);
v___x_1726_ = v___x_1721_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_1729_, lean_object* v_declHint_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1729_, v_declHint_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1735_, lean_object* v_msg_1736_, lean_object* v_declHint_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v_a_1742_; lean_object* v___x_1743_; 
v___x_1741_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1736_, v_declHint_1737_, v___y_1738_, v___y_1739_);
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1735_, v_a_1742_, v___y_1738_, v___y_1739_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1744_, lean_object* v_msg_1745_, lean_object* v_declHint_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1744_, v_msg_1745_, v_declHint_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v_ref_1744_);
return v_res_1750_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2));
v___x_1756_ = l_Lean_stringToMessageData(v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1757_, lean_object* v_constName_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1762_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1763_ = 0;
lean_inc(v_constName_1758_);
v___x_1764_ = l_Lean_MessageData_ofConstName(v_constName_1758_, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1762_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1757_, v___x_1767_, v_constName_1758_, v___y_1759_, v___y_1760_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1769_, lean_object* v_constName_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1769_, v_constName_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v_ref_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_ref_1779_; lean_object* v___x_1780_; 
v_ref_1779_ = lean_ctor_get(v___y_1776_, 5);
v___x_1780_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1779_, v_constName_1775_, v___y_1776_, v___y_1777_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object* v_constName_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_env_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = lean_st_ref_get(v___y_1788_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1792_ = 0;
lean_inc(v_constName_1786_);
v___x_1793_ = l_Lean_Environment_findConstVal_x3f(v_env_1791_, v_constName_1786_, v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1786_, v___y_1787_, v___y_1788_);
return v___x_1794_;
}
else
{
lean_object* v_val_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_constName_1786_);
v_val_1795_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1793_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_val_1795_);
lean_dec(v___x_1793_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 0);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_val_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object* v_constName_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object* v_constName_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
lean_inc(v_constName_1808_);
v___x_1812_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1824_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1824_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1824_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_levelParams_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v_levelParams_1817_ = lean_ctor_get(v_a_1813_, 1);
lean_inc(v_levelParams_1817_);
lean_dec(v_a_1813_);
v___x_1818_ = lean_box(0);
v___x_1819_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(v_levelParams_1817_, v___x_1818_);
v___x_1820_ = l_Lean_mkConst(v_constName_1808_, v___x_1819_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1820_);
v___x_1822_ = v___x_1815_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_constName_1808_);
v_a_1825_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1812_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1812_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object* v_constName_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_constName_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__1(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__0));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__3(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__2));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__5(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__4));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__7(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__6));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__9(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__8));
v___x_1852_ = l_Lean_stringToMessageData(v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__11(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__10));
v___x_1855_ = l_Lean_stringToMessageData(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object* v_declName_1856_, lean_object* v_warning_1857_, uint8_t v_useErrorFormat_1858_, lean_object* v_filePath_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___y_1864_; lean_object* v___y_1865_; 
if (v_useErrorFormat_1858_ == 0)
{
lean_dec_ref(v_filePath_1859_);
v___y_1864_ = v_a_1860_;
v___y_1865_ = v_a_1861_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1885_; 
lean_inc(v_declName_1856_);
v___x_1885_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1856_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
if (lean_obj_tag(v_a_1886_) == 1)
{
lean_object* v_val_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1943_; 
v_val_1887_ = lean_ctor_get(v_a_1886_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1889_ = v_a_1886_;
v_isShared_1890_ = v_isSharedCheck_1943_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_val_1887_);
lean_dec(v_a_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1943_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1856_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_range_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1933_; 
v_range_1892_ = lean_ctor_get(v_val_1887_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_val_1887_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v_val_1887_, 1);
lean_dec(v_unused_1934_);
v___x_1894_ = v_val_1887_;
v_isShared_1895_ = v_isSharedCheck_1933_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_range_1892_);
lean_dec(v_val_1887_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1933_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_pos_1896_; lean_object* v_a_1897_; lean_object* v_line_1898_; lean_object* v_column_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1932_; 
v_pos_1896_ = lean_ctor_get(v_range_1892_, 0);
lean_inc_ref(v_pos_1896_);
lean_dec_ref(v_range_1892_);
v_a_1897_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1891_);
v_line_1898_ = lean_ctor_get(v_pos_1896_, 0);
v_column_1899_ = lean_ctor_get(v_pos_1896_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_pos_1896_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1901_ = v_pos_1896_;
v_isShared_1902_ = v_isSharedCheck_1932_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_column_1899_);
lean_inc(v_line_1898_);
lean_dec(v_pos_1896_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1932_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 3);
lean_ctor_set(v___x_1889_, 0, v_filePath_1859_);
v___x_1904_ = v___x_1889_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_filePath_1859_);
v___x_1904_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = l_Lean_MessageData_ofFormat(v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__7, &l_Lean_Linter_EnvLinter_printWarning___closed__7_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__7);
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 7);
lean_ctor_set(v___x_1901_, 1, v___x_1906_);
lean_ctor_set(v___x_1901_, 0, v___x_1905_);
v___x_1908_ = v___x_1901_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1909_ = l_Nat_reprFast(v_line_1898_);
v___x_1910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
v___x_1911_ = l_Lean_MessageData_ofFormat(v___x_1910_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 7);
lean_ctor_set(v___x_1894_, 1, v___x_1911_);
lean_ctor_set(v___x_1894_, 0, v___x_1908_);
v___x_1913_ = v___x_1894_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1906_);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_column_1899_, v___x_1915_);
lean_dec(v_column_1899_);
v___x_1917_ = l_Nat_reprFast(v___x_1916_);
v___x_1918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
v___x_1919_ = l_Lean_MessageData_ofFormat(v___x_1918_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1914_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__9, &l_Lean_Linter_EnvLinter_printWarning___closed__9_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__9);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_MessageData_ofExpr(v_a_1897_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__11, &l_Lean_Linter_EnvLinter_printWarning___closed__11_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__11);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v_warning_1857_);
v___x_1928_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1927_, v_a_1860_, v_a_1861_);
return v___x_1928_;
}
}
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_del_object(v___x_1889_);
lean_dec(v_val_1887_);
lean_dec_ref(v_filePath_1859_);
lean_dec_ref(v_warning_1857_);
v_a_1935_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1891_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1891_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
else
{
lean_dec(v_a_1886_);
lean_dec_ref(v_filePath_1859_);
v___y_1864_ = v_a_1860_;
v___y_1865_ = v_a_1861_;
goto v___jp_1863_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_filePath_1859_);
lean_dec_ref(v_warning_1857_);
lean_dec(v_declName_1856_);
v_a_1944_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1885_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1885_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
v___jp_1863_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1856_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref(v___x_1866_);
v___x_1868_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__1, &l_Lean_Linter_EnvLinter_printWarning___closed__1_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__1);
v___x_1869_ = l_Lean_MessageData_ofExpr(v_a_1867_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__3, &l_Lean_Linter_EnvLinter_printWarning___closed__3_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__3);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v_warning_1857_);
v___x_1874_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1875_, v___y_1864_, v___y_1865_);
return v___x_1876_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_warning_1857_);
v_a_1877_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1866_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1866_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object* v_declName_1952_, lean_object* v_warning_1953_, lean_object* v_useErrorFormat_1954_, lean_object* v_filePath_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
uint8_t v_useErrorFormat_boxed_1959_; lean_object* v_res_1960_; 
v_useErrorFormat_boxed_1959_ = lean_unbox(v_useErrorFormat_1954_);
v_res_1960_ = l_Lean_Linter_EnvLinter_printWarning(v_declName_1952_, v_warning_1953_, v_useErrorFormat_boxed_1959_, v_filePath_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1961_, lean_object* v_constName_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1962_, v___y_1963_, v___y_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1967_, lean_object* v_constName_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(v_00_u03b1_1967_, v_constName_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1973_, lean_object* v_ref_1974_, lean_object* v_constName_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1974_, v_constName_1975_, v___y_1976_, v___y_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1980_, lean_object* v_ref_1981_, lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1980_, v_ref_1981_, v_constName_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v_ref_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1987_, lean_object* v_ref_1988_, lean_object* v_msg_1989_, lean_object* v_declHint_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1988_, v_msg_1989_, v_declHint_1990_, v___y_1991_, v___y_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1995_, lean_object* v_ref_1996_, lean_object* v_msg_1997_, lean_object* v_declHint_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1995_, v_ref_1996_, v_msg_1997_, v_declHint_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v_ref_1996_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_2003_, lean_object* v_declHint_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_2003_, v_declHint_2004_, v___y_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2009_, lean_object* v_declHint_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_2009_, v_declHint_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2015_, lean_object* v_ref_2016_, lean_object* v_msg_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_2016_, v_msg_2017_, v___y_2018_, v___y_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_ref_2023_, lean_object* v_msg_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2022_, v_ref_2023_, v_msg_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v_ref_2023_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2029_, lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_2030_, v___y_2031_, v___y_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_msg_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_2035_, v_msg_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t v_useErrorFormat_2041_, lean_object* v_filePath_2042_, size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_bs_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec_ref(v_filePath_2042_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_bs_2045_);
return v___x_2050_;
}
else
{
lean_object* v_v_2051_; lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v___x_2054_; 
v_v_2051_ = lean_array_uget_borrowed(v_bs_2045_, v_i_2044_);
v_fst_2052_ = lean_ctor_get(v_v_2051_, 0);
v_snd_2053_ = lean_ctor_get(v_v_2051_, 1);
lean_inc_ref(v_filePath_2042_);
lean_inc(v_snd_2053_);
lean_inc(v_fst_2052_);
v___x_2054_ = l_Lean_Linter_EnvLinter_printWarning(v_fst_2052_, v_snd_2053_, v_useErrorFormat_2041_, v_filePath_2042_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v_bs_x27_2057_; size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = lean_unsigned_to_nat(0u);
v_bs_x27_2057_ = lean_array_uset(v_bs_2045_, v_i_2044_, v___x_2056_);
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2044_, v___x_2058_);
v___x_2060_ = lean_array_uset(v_bs_x27_2057_, v_i_2044_, v_a_2055_);
v_i_2044_ = v___x_2059_;
v_bs_2045_ = v___x_2060_;
goto _start;
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_bs_2045_);
lean_dec_ref(v_filePath_2042_);
v_a_2062_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2054_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2054_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object* v_useErrorFormat_2070_, lean_object* v_filePath_2071_, lean_object* v_sz_2072_, lean_object* v_i_2073_, lean_object* v_bs_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
uint8_t v_useErrorFormat_boxed_2078_; size_t v_sz_boxed_2079_; size_t v_i_boxed_2080_; lean_object* v_res_2081_; 
v_useErrorFormat_boxed_2078_ = lean_unbox(v_useErrorFormat_2070_);
v_sz_boxed_2079_ = lean_unbox_usize(v_sz_2072_);
lean_dec(v_sz_2072_);
v_i_boxed_2080_ = lean_unbox_usize(v_i_2073_);
lean_dec(v_i_2073_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_boxed_2078_, v_filePath_2071_, v_sz_boxed_2079_, v_i_boxed_2080_, v_bs_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2081_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_box(1);
v___x_2083_ = l_Lean_MessageData_ofFormat(v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object* v_results_2084_, lean_object* v_filePath_2085_, uint8_t v_useErrorFormat_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_2084_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v_sz_2092_ = lean_array_size(v_a_2091_);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_2086_, v_filePath_2085_, v_sz_2092_, v___x_2093_, v_a_2091_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2105_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2099_ = lean_array_to_list(v_a_2095_);
v___x_2100_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2101_ = l_Lean_MessageData_joinSep(v___x_2099_, v___x_2100_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2101_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2094_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2094_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v_filePath_2085_);
v_a_2114_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2090_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2090_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object* v_results_2122_, lean_object* v_filePath_2123_, lean_object* v_useErrorFormat_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
uint8_t v_useErrorFormat_boxed_2128_; lean_object* v_res_2129_; 
v_useErrorFormat_boxed_2128_ = lean_unbox(v_useErrorFormat_2124_);
v_res_2129_ = l_Lean_Linter_EnvLinter_printWarnings(v_results_2122_, v_filePath_2123_, v_useErrorFormat_boxed_2128_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_results_2122_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 0)
{
return v_x_2130_;
}
else
{
lean_object* v_key_2132_; lean_object* v_value_2133_; lean_object* v_tail_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_key_2132_ = lean_ctor_get(v_x_2131_, 0);
v_value_2133_ = lean_ctor_get(v_x_2131_, 1);
v_tail_2134_ = lean_ctor_get(v_x_2131_, 2);
lean_inc(v_value_2133_);
lean_inc(v_key_2132_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v_key_2132_);
lean_ctor_set(v___x_2135_, 1, v_value_2133_);
v___x_2136_ = lean_array_push(v_x_2130_, v___x_2135_);
v_x_2130_ = v___x_2136_;
v_x_2131_ = v_tail_2134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_x_2138_, v_x_2139_);
lean_dec(v_x_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object* v_as_2141_, size_t v_i_2142_, size_t v_stop_2143_, lean_object* v_b_2144_){
_start:
{
uint8_t v___x_2145_; 
v___x_2145_ = lean_usize_dec_eq(v_i_2142_, v_stop_2143_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; 
v___x_2146_ = lean_array_uget_borrowed(v_as_2141_, v_i_2142_);
v___x_2147_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_b_2144_, v___x_2146_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2142_, v___x_2148_);
v_i_2142_ = v___x_2149_;
v_b_2144_ = v___x_2147_;
goto _start;
}
else
{
return v_b_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object* v_as_2151_, lean_object* v_i_2152_, lean_object* v_stop_2153_, lean_object* v_b_2154_){
_start:
{
size_t v_i_boxed_2155_; size_t v_stop_boxed_2156_; lean_object* v_res_2157_; 
v_i_boxed_2155_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_stop_boxed_2156_ = lean_unbox_usize(v_stop_2153_);
lean_dec(v_stop_2153_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_as_2151_, v_i_boxed_2155_, v_stop_boxed_2156_, v_b_2154_);
lean_dec_ref(v_as_2151_);
return v_res_2157_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t v_useErrorFormat_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
if (lean_obj_tag(v_x_2165_) == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = l_List_reverse___redArg(v_x_2166_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
else
{
lean_object* v_head_2172_; lean_object* v_tail_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2216_; 
v_head_2172_ = lean_ctor_get(v_x_2165_, 0);
v_tail_2173_ = lean_ctor_get(v_x_2165_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_x_2165_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2175_ = v_x_2165_;
v_isShared_2176_ = v_isSharedCheck_2216_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_tail_2173_);
lean_inc(v_head_2172_);
lean_dec(v_x_2165_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2216_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_a_2178_; lean_object* v_snd_2183_; lean_object* v_fst_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2215_; 
v_snd_2183_ = lean_ctor_get(v_head_2172_, 1);
v_fst_2184_ = lean_ctor_get(v_head_2172_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_head_2172_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2186_ = v_head_2172_;
v_isShared_2187_ = v_isSharedCheck_2215_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2183_);
lean_inc(v_fst_2184_);
lean_dec(v_head_2172_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2215_;
goto v_resetjp_2185_;
}
v___jp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_x_2166_);
lean_ctor_set(v___x_2175_, 0, v_a_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2178_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_x_2166_);
v___x_2180_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
v_x_2165_ = v_tail_2173_;
v_x_2166_ = v___x_2180_;
goto _start;
}
}
v_resetjp_2185_:
{
lean_object* v_fst_2188_; lean_object* v_snd_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2214_; 
v_fst_2188_ = lean_ctor_get(v_snd_2183_, 0);
v_snd_2189_ = lean_ctor_get(v_snd_2183_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_snd_2183_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2191_ = v_snd_2183_;
v_isShared_2192_ = v_isSharedCheck_2214_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_snd_2189_);
lean_inc(v_fst_2188_);
lean_dec(v_snd_2183_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2214_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2189_, v_fst_2188_, v_useErrorFormat_2164_, v___y_2167_, v___y_2168_);
lean_dec(v_snd_2189_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1);
v___x_2196_ = l_Lean_MessageData_ofName(v_fst_2184_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 7);
lean_ctor_set(v___x_2191_, 1, v___x_2196_);
lean_ctor_set(v___x_2191_, 0, v___x_2195_);
v___x_2198_ = v___x_2191_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
if (v_isShared_2187_ == 0)
{
lean_ctor_set_tag(v___x_2186_, 7);
lean_ctor_set(v___x_2186_, 1, v___x_2199_);
lean_ctor_set(v___x_2186_, 0, v___x_2198_);
v___x_2201_ = v___x_2186_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_a_2194_);
v_a_2178_ = v___x_2202_;
goto v___jp_2177_;
}
}
}
else
{
lean_del_object(v___x_2191_);
lean_del_object(v___x_2186_);
lean_dec(v_fst_2184_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2193_);
v_a_2178_ = v_a_2205_;
goto v___jp_2177_;
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2175_);
lean_dec(v_tail_2173_);
lean_dec(v_x_2166_);
v_a_2206_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2193_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2193_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object* v_useErrorFormat_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v_useErrorFormat_boxed_2223_; lean_object* v_res_2224_; 
v_useErrorFormat_boxed_2223_ = lean_unbox(v_useErrorFormat_2217_);
v_res_2224_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_boxed_2223_, v_x_2218_, v_x_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object* v_a_2225_, lean_object* v_x_2226_){
_start:
{
if (lean_obj_tag(v_x_2226_) == 0)
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_box(0);
return v___x_2227_;
}
else
{
lean_object* v_key_2228_; lean_object* v_value_2229_; lean_object* v_tail_2230_; uint8_t v___x_2231_; 
v_key_2228_ = lean_ctor_get(v_x_2226_, 0);
v_value_2229_ = lean_ctor_get(v_x_2226_, 1);
v_tail_2230_ = lean_ctor_get(v_x_2226_, 2);
v___x_2231_ = lean_name_eq(v_key_2228_, v_a_2225_);
if (v___x_2231_ == 0)
{
v_x_2226_ = v_tail_2230_;
goto _start;
}
else
{
lean_object* v___x_2233_; 
lean_inc(v_value_2229_);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_value_2229_);
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object* v_a_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2234_, v_x_2235_);
lean_dec(v_x_2235_);
lean_dec(v_a_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object* v_m_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_buckets_2239_; lean_object* v___x_2240_; uint64_t v___y_2242_; 
v_buckets_2239_ = lean_ctor_get(v_m_2237_, 1);
v___x_2240_ = lean_array_get_size(v_buckets_2239_);
if (lean_obj_tag(v_a_2238_) == 0)
{
uint64_t v___x_2256_; 
v___x_2256_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_2242_ = v___x_2256_;
goto v___jp_2241_;
}
else
{
uint64_t v_hash_2257_; 
v_hash_2257_ = lean_ctor_get_uint64(v_a_2238_, sizeof(void*)*2);
v___y_2242_ = v_hash_2257_;
goto v___jp_2241_;
}
v___jp_2241_:
{
uint64_t v___x_2243_; uint64_t v___x_2244_; uint64_t v_fold_2245_; uint64_t v___x_2246_; uint64_t v___x_2247_; uint64_t v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2243_ = 32ULL;
v___x_2244_ = lean_uint64_shift_right(v___y_2242_, v___x_2243_);
v_fold_2245_ = lean_uint64_xor(v___y_2242_, v___x_2244_);
v___x_2246_ = 16ULL;
v___x_2247_ = lean_uint64_shift_right(v_fold_2245_, v___x_2246_);
v___x_2248_ = lean_uint64_xor(v_fold_2245_, v___x_2247_);
v___x_2249_ = lean_uint64_to_usize(v___x_2248_);
v___x_2250_ = lean_usize_of_nat(v___x_2240_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_sub(v___x_2250_, v___x_2251_);
v___x_2253_ = lean_usize_land(v___x_2249_, v___x_2252_);
v___x_2254_ = lean_array_uget_borrowed(v_buckets_2239_, v___x_2253_);
v___x_2255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2238_, v___x_2254_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object* v_m_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_m_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object* v_key_2261_, lean_object* v_value_2262_, lean_object* v_fp_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v___x_2267_, v_key_2261_, v_value_2262_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_fp_2263_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object* v_key_2271_, lean_object* v_value_2272_, lean_object* v_fp_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2271_, v_value_2272_, v_fp_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object* v_constName_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v_env_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = lean_st_ref_get(v___y_2280_);
v_env_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_ref(v_env_2283_);
lean_dec(v___x_2282_);
v___x_2284_ = 0;
lean_inc(v_constName_2278_);
v___x_2285_ = l_Lean_Environment_find_x3f(v_env_2283_, v_constName_2278_, v___x_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_2278_, v___y_2279_, v___y_2280_);
return v___x_2286_;
}
else
{
lean_object* v_val_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_constName_2278_);
v_val_2287_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2285_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_val_2287_);
lean_dec(v___x_2285_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set_tag(v___x_2289_, 0);
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_val_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object* v_constName_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_constName_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object* v_declName_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; 
lean_inc(v_declName_2300_);
v___x_2304_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_declName_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2331_; 
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2332_);
v___x_2306_ = v___x_2304_;
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v___x_2304_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v_env_2309_; lean_object* v___x_2310_; 
v___x_2308_ = lean_st_ref_get(v___y_2302_);
v_env_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_ref(v_env_2309_);
lean_dec(v___x_2308_);
v___x_2310_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2309_, v_declName_2300_);
lean_dec(v_declName_2300_);
lean_dec_ref(v_env_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_box(0);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2311_);
v___x_2313_ = v___x_2306_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
else
{
lean_object* v_val_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2330_; 
v_val_2315_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2317_ = v___x_2310_;
v_isShared_2318_ = v_isSharedCheck_2330_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_val_2315_);
lean_dec(v___x_2310_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2330_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v_env_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2319_ = lean_st_ref_get(v___y_2302_);
v_env_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc_ref(v_env_2320_);
lean_dec(v___x_2319_);
v___x_2321_ = lean_box(0);
v___x_2322_ = l_Lean_Environment_allImportedModuleNames(v_env_2320_);
lean_dec_ref(v_env_2320_);
v___x_2323_ = lean_array_get(v___x_2321_, v___x_2322_, v_val_2315_);
lean_dec(v_val_2315_);
lean_dec_ref(v___x_2322_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2323_);
v___x_2325_ = v___x_2317_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2325_);
v___x_2327_ = v___x_2306_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_declName_2300_);
v_a_2333_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2304_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2304_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object* v_declName_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_declName_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t v_useErrorFormat_2349_, lean_object* v_sp_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
if (lean_obj_tag(v_x_2352_) == 0)
{
lean_object* v___x_2356_; 
lean_dec(v_sp_2350_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_x_2351_);
return v___x_2356_;
}
else
{
lean_object* v_key_2357_; lean_object* v_value_2358_; lean_object* v_tail_2359_; lean_object* v___y_2361_; lean_object* v_a_2362_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___x_2369_; 
v_key_2357_ = lean_ctor_get(v_x_2352_, 0);
lean_inc_n(v_key_2357_, 2);
v_value_2358_ = lean_ctor_get(v_x_2352_, 1);
lean_inc(v_value_2358_);
v_tail_2359_ = lean_ctor_get(v_x_2352_, 2);
lean_inc(v_tail_2359_);
lean_dec_ref(v_x_2352_);
v___x_2369_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_key_2357_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; lean_object* v___y_2373_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = lean_st_ref_get(v___y_2354_);
if (lean_obj_tag(v_a_2370_) == 0)
{
lean_object* v_env_2409_; lean_object* v___x_2410_; 
v_env_2409_ = lean_ctor_get(v___x_2371_, 0);
lean_inc_ref(v_env_2409_);
lean_dec(v___x_2371_);
v___x_2410_ = l_Lean_Environment_mainModule(v_env_2409_);
lean_dec_ref(v_env_2409_);
v___y_2373_ = v___x_2410_;
goto v___jp_2372_;
}
else
{
lean_object* v_val_2411_; 
lean_dec(v___x_2371_);
v_val_2411_ = lean_ctor_get(v_a_2370_, 0);
lean_inc(v_val_2411_);
lean_dec_ref(v_a_2370_);
v___y_2373_ = v_val_2411_;
goto v___jp_2372_;
}
v___jp_2372_:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_x_2351_, v___y_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
if (v_useErrorFormat_2349_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2376_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2357_, v_value_2358_, v___x_2375_, v___y_2353_, v___y_2354_);
v___y_2366_ = v___y_2373_;
v___y_2367_ = v___x_2376_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1));
lean_inc(v___y_2373_);
lean_inc(v_sp_2350_);
v___x_2378_ = l_Lean_SearchPath_findWithExt(v_sp_2350_, v___x_2377_, v___y_2373_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2378_);
if (lean_obj_tag(v_a_2379_) == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2));
lean_inc(v___y_2373_);
v___x_2381_ = l_Lean_modToFilePath(v___x_2380_, v___y_2373_, v___x_2377_);
v___x_2382_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2357_, v_value_2358_, v___x_2381_, v___y_2353_, v___y_2354_);
v___y_2366_ = v___y_2373_;
v___y_2367_ = v___x_2382_;
goto v___jp_2365_;
}
else
{
lean_object* v_val_2383_; lean_object* v___x_2384_; 
v_val_2383_ = lean_ctor_get(v_a_2379_, 0);
lean_inc(v_val_2383_);
lean_dec_ref(v_a_2379_);
v___x_2384_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2357_, v_value_2358_, v_val_2383_, v___y_2353_, v___y_2354_);
v___y_2366_ = v___y_2373_;
v___y_2367_ = v___x_2384_;
goto v___jp_2365_;
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v___y_2373_);
lean_dec(v_tail_2359_);
lean_dec(v_value_2358_);
lean_dec(v_key_2357_);
lean_dec_ref(v_x_2351_);
lean_dec(v_sp_2350_);
v_a_2385_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2387_ = v___x_2378_;
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2378_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_ref_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v_ref_2389_ = lean_ctor_get(v___y_2353_, 5);
v___x_2390_ = lean_io_error_to_string(v_a_2385_);
v___x_2391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
v___x_2392_ = l_Lean_MessageData_ofFormat(v___x_2391_);
lean_inc(v_ref_2389_);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_ref_2389_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2393_);
v___x_2395_ = v___x_2387_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
else
{
lean_object* v_val_2398_; lean_object* v_fst_2399_; lean_object* v_snd_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_val_2398_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_val_2398_);
lean_dec_ref(v___x_2374_);
v_fst_2399_ = lean_ctor_get(v_val_2398_, 0);
v_snd_2400_ = lean_ctor_get(v_val_2398_, 1);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_val_2398_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v_val_2398_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snd_2400_);
lean_inc(v_fst_2399_);
lean_dec(v_val_2398_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_snd_2400_, v_key_2357_, v_value_2358_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_fst_2399_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
v___y_2361_ = v___y_2373_;
v_a_2362_ = v___x_2406_;
goto v___jp_2360_;
}
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_tail_2359_);
lean_dec(v_value_2358_);
lean_dec(v_key_2357_);
lean_dec_ref(v_x_2351_);
lean_dec(v_sp_2350_);
v_a_2412_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2369_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2369_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
v___jp_2360_:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_x_2351_, v___y_2361_, v_a_2362_);
v_x_2351_ = v___x_2363_;
v_x_2352_ = v_tail_2359_;
goto _start;
}
v___jp_2365_:
{
lean_object* v_a_2368_; 
v_a_2368_ = lean_ctor_get(v___y_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref(v___y_2367_);
v___y_2361_ = v___y_2366_;
v_a_2362_ = v_a_2368_;
goto v___jp_2360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object* v_useErrorFormat_2420_, lean_object* v_sp_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
uint8_t v_useErrorFormat_boxed_2427_; lean_object* v_res_2428_; 
v_useErrorFormat_boxed_2427_ = lean_unbox(v_useErrorFormat_2420_);
v_res_2428_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_boxed_2427_, v_sp_2421_, v_x_2422_, v_x_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t v_useErrorFormat_2429_, lean_object* v_sp_2430_, lean_object* v_as_2431_, size_t v_i_2432_, size_t v_stop_2433_, lean_object* v_b_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_eq(v_i_2432_, v_stop_2433_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_array_uget_borrowed(v_as_2431_, v_i_2432_);
lean_inc(v___x_2439_);
lean_inc(v_sp_2430_);
v___x_2440_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_2429_, v_sp_2430_, v_b_2434_, v___x_2439_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; size_t v___x_2442_; size_t v___x_2443_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2432_, v___x_2442_);
v_i_2432_ = v___x_2443_;
v_b_2434_ = v_a_2441_;
goto _start;
}
else
{
lean_dec(v_sp_2430_);
return v___x_2440_;
}
}
else
{
lean_object* v___x_2445_; 
lean_dec(v_sp_2430_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_b_2434_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object* v_useErrorFormat_2446_, lean_object* v_sp_2447_, lean_object* v_as_2448_, lean_object* v_i_2449_, lean_object* v_stop_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v_useErrorFormat_boxed_2455_; size_t v_i_boxed_2456_; size_t v_stop_boxed_2457_; lean_object* v_res_2458_; 
v_useErrorFormat_boxed_2455_ = lean_unbox(v_useErrorFormat_2446_);
v_i_boxed_2456_ = lean_unbox_usize(v_i_2449_);
lean_dec(v_i_2449_);
v_stop_boxed_2457_ = lean_unbox_usize(v_stop_2450_);
lean_dec(v_stop_2450_);
v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_boxed_2455_, v_sp_2447_, v_as_2448_, v_i_boxed_2456_, v_stop_boxed_2457_, v_b_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec_ref(v_as_2448_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object* v_hi_2459_, lean_object* v_pivot_2460_, lean_object* v_as_2461_, lean_object* v_i_2462_, lean_object* v_k_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_nat_dec_lt(v_k_2463_, v_hi_2459_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec(v_k_2463_);
lean_dec_ref(v_pivot_2460_);
v___x_2465_ = lean_array_fswap(v_as_2461_, v_i_2462_, v_hi_2459_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_i_2462_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v_fst_2468_; lean_object* v_fst_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2467_ = lean_array_fget_borrowed(v_as_2461_, v_k_2463_);
v_fst_2468_ = lean_ctor_get(v___x_2467_, 0);
v_fst_2469_ = lean_ctor_get(v_pivot_2460_, 0);
lean_inc(v_fst_2468_);
v___x_2470_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2468_, v___x_2464_);
lean_inc(v_fst_2469_);
v___x_2471_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2469_, v___x_2464_);
v___x_2472_ = lean_string_dec_lt(v___x_2470_, v___x_2471_);
lean_dec_ref(v___x_2471_);
lean_dec_ref(v___x_2470_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_unsigned_to_nat(1u);
v___x_2474_ = lean_nat_add(v_k_2463_, v___x_2473_);
lean_dec(v_k_2463_);
v_k_2463_ = v___x_2474_;
goto _start;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_array_fswap(v_as_2461_, v_i_2462_, v_k_2463_);
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_nat_add(v_i_2462_, v___x_2477_);
lean_dec(v_i_2462_);
v___x_2479_ = lean_nat_add(v_k_2463_, v___x_2477_);
lean_dec(v_k_2463_);
v_as_2461_ = v___x_2476_;
v_i_2462_ = v___x_2478_;
v_k_2463_ = v___x_2479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object* v_hi_2481_, lean_object* v_pivot_2482_, lean_object* v_as_2483_, lean_object* v_i_2484_, lean_object* v_k_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2481_, v_pivot_2482_, v_as_2483_, v_i_2484_, v_k_2485_);
lean_dec(v_hi_2481_);
return v_res_2486_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t v___x_2487_, lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
lean_object* v_fst_2490_; lean_object* v_fst_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_fst_2490_ = lean_ctor_get(v_x_2488_, 0);
lean_inc(v_fst_2490_);
lean_dec_ref(v_x_2488_);
v_fst_2491_ = lean_ctor_get(v_x_2489_, 0);
lean_inc(v_fst_2491_);
lean_dec_ref(v_x_2489_);
v___x_2492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2490_, v___x_2487_);
v___x_2493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2491_, v___x_2487_);
v___x_2494_ = lean_string_dec_lt(v___x_2492_, v___x_2493_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object* v___x_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
uint8_t v___x_5444__boxed_2498_; uint8_t v_res_2499_; lean_object* v_r_2500_; 
v___x_5444__boxed_2498_ = lean_unbox(v___x_2495_);
v_res_2499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_5444__boxed_2498_, v_x_2496_, v_x_2497_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object* v_n_2501_, lean_object* v_as_2502_, lean_object* v_lo_2503_, lean_object* v_hi_2504_){
_start:
{
lean_object* v___y_2506_; uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_lt(v_lo_2503_, v_hi_2504_);
if (v___x_2516_ == 0)
{
lean_dec(v_lo_2503_);
return v_as_2502_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_mid_2519_; lean_object* v___y_2521_; lean_object* v___y_2527_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2517_ = lean_nat_add(v_lo_2503_, v_hi_2504_);
v___x_2518_ = lean_unsigned_to_nat(1u);
v_mid_2519_ = lean_nat_shiftr(v___x_2517_, v___x_2518_);
lean_dec(v___x_2517_);
v___x_2532_ = lean_array_fget_borrowed(v_as_2502_, v_mid_2519_);
v___x_2533_ = lean_array_fget_borrowed(v_as_2502_, v_lo_2503_);
lean_inc(v___x_2533_);
lean_inc(v___x_2532_);
v___x_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2516_, v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
v___y_2527_ = v_as_2502_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_array_fswap(v_as_2502_, v_lo_2503_, v_mid_2519_);
v___y_2527_ = v___x_2535_;
goto v___jp_2526_;
}
v___jp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2522_ = lean_array_fget_borrowed(v___y_2521_, v_mid_2519_);
v___x_2523_ = lean_array_fget_borrowed(v___y_2521_, v_hi_2504_);
lean_inc(v___x_2523_);
lean_inc(v___x_2522_);
v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2516_, v___x_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_dec(v_mid_2519_);
v___y_2506_ = v___y_2521_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_array_fswap(v___y_2521_, v_mid_2519_, v_hi_2504_);
lean_dec(v_mid_2519_);
v___y_2506_ = v___x_2525_;
goto v___jp_2505_;
}
}
v___jp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2528_ = lean_array_fget_borrowed(v___y_2527_, v_hi_2504_);
v___x_2529_ = lean_array_fget_borrowed(v___y_2527_, v_lo_2503_);
lean_inc(v___x_2529_);
lean_inc(v___x_2528_);
v___x_2530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2516_, v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
v___y_2521_ = v___y_2527_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_array_fswap(v___y_2527_, v_lo_2503_, v_hi_2504_);
v___y_2521_ = v___x_2531_;
goto v___jp_2520_;
}
}
}
v___jp_2505_:
{
lean_object* v_pivot_2507_; lean_object* v___x_2508_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; uint8_t v___x_2511_; 
v_pivot_2507_ = lean_array_fget(v___y_2506_, v_hi_2504_);
lean_inc_n(v_lo_2503_, 2);
v___x_2508_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2504_, v_pivot_2507_, v___y_2506_, v_lo_2503_, v_lo_2503_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_fst_2509_);
v_snd_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2508_);
v___x_2511_ = lean_nat_dec_le(v_hi_2504_, v_fst_2509_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2501_, v_snd_2510_, v_lo_2503_, v_fst_2509_);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v_fst_2509_, v___x_2513_);
lean_dec(v_fst_2509_);
v_as_2502_ = v___x_2512_;
v_lo_2503_ = v___x_2514_;
goto _start;
}
else
{
lean_dec(v_fst_2509_);
lean_dec(v_lo_2503_);
return v_snd_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object* v_n_2536_, lean_object* v_as_2537_, lean_object* v_lo_2538_, lean_object* v_hi_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2536_, v_as_2537_, v_lo_2538_, v_hi_2539_);
lean_dec(v_hi_2539_);
lean_dec(v_n_2536_);
return v_res_2540_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object* v_results_2543_, uint8_t v_useErrorFormat_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v_size_2602_; lean_object* v_buckets_2603_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_sp_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; 
if (v_useErrorFormat_2544_ == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_box(0);
v_sp_2631_ = v___x_2647_;
v___y_2632_ = v_a_2545_;
v___y_2633_ = v_a_2546_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v_sp_2631_ = v_a_2649_;
v___y_2632_ = v_a_2545_;
v___y_2633_ = v_a_2546_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2662_; 
v_a_2650_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2652_ = v___x_2648_;
v_isShared_2653_ = v_isSharedCheck_2662_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2648_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2662_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_ref_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v_ref_2654_ = lean_ctor_get(v_a_2545_, 5);
v___x_2655_ = lean_io_error_to_string(v_a_2650_);
v___x_2656_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
v___x_2657_ = l_Lean_MessageData_ofFormat(v___x_2656_);
lean_inc(v_ref_2654_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_ref_2654_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2658_);
v___x_2660_ = v___x_2652_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
v___jp_2548_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_array_to_list(v___y_2551_);
v___x_2553_ = lean_box(0);
v___x_2554_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_2544_, v___x_2552_, v___x_2553_, v___y_2550_, v___y_2549_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2564_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2564_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2564_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2559_ = lean_obj_once(&l_Lean_Linter_EnvLinter_groupedByFilename___closed__0, &l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once, _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0);
v___x_2560_ = l_Lean_MessageData_joinSep(v_a_2555_, v___x_2559_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2560_);
v___x_2562_ = v___x_2557_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2554_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2554_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
v___jp_2573_:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v___y_2574_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec(v___y_2574_);
v___y_2549_ = v___y_2576_;
v___y_2550_ = v___y_2575_;
v___y_2551_ = v___x_2580_;
goto v___jp_2548_;
}
v___jp_2581_:
{
uint8_t v___x_2588_; 
v___x_2588_ = lean_nat_dec_le(v___y_2587_, v___y_2583_);
if (v___x_2588_ == 0)
{
lean_dec(v___y_2583_);
lean_inc(v___y_2587_);
v___y_2574_ = v___y_2582_;
v___y_2575_ = v___y_2585_;
v___y_2576_ = v___y_2584_;
v___y_2577_ = v___y_2586_;
v___y_2578_ = v___y_2587_;
v___y_2579_ = v___y_2587_;
goto v___jp_2573_;
}
else
{
v___y_2574_ = v___y_2582_;
v___y_2575_ = v___y_2585_;
v___y_2576_ = v___y_2584_;
v___y_2577_ = v___y_2586_;
v___y_2578_ = v___y_2587_;
v___y_2579_ = v___y_2583_;
goto v___jp_2573_;
}
}
v___jp_2589_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2593_ = lean_array_get_size(v___y_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_nat_dec_eq(v___x_2593_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_nat_sub(v___x_2593_, v___x_2596_);
v___x_2598_ = lean_nat_dec_le(v___x_2594_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_inc(v___x_2597_);
v___y_2582_ = v___x_2593_;
v___y_2583_ = v___x_2597_;
v___y_2584_ = v___y_2591_;
v___y_2585_ = v___y_2590_;
v___y_2586_ = v___y_2592_;
v___y_2587_ = v___x_2597_;
goto v___jp_2581_;
}
else
{
v___y_2582_ = v___x_2593_;
v___y_2583_ = v___x_2597_;
v___y_2584_ = v___y_2591_;
v___y_2585_ = v___y_2590_;
v___y_2586_ = v___y_2592_;
v___y_2587_ = v___x_2594_;
goto v___jp_2581_;
}
}
else
{
v___y_2549_ = v___y_2591_;
v___y_2550_ = v___y_2590_;
v___y_2551_ = v___y_2592_;
goto v___jp_2548_;
}
}
v___jp_2599_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2604_ = lean_mk_empty_array_with_capacity(v_size_2602_);
lean_dec(v_size_2602_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_array_get_size(v_buckets_2603_);
v___x_2607_ = lean_nat_dec_lt(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_dec_ref(v_buckets_2603_);
v___y_2590_ = v___y_2600_;
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___x_2604_;
goto v___jp_2589_;
}
else
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_nat_dec_le(v___x_2606_, v___x_2606_);
if (v___x_2608_ == 0)
{
if (v___x_2607_ == 0)
{
lean_dec_ref(v_buckets_2603_);
v___y_2590_ = v___y_2600_;
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___x_2604_;
goto v___jp_2589_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2606_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2603_, v___x_2609_, v___x_2610_, v___x_2604_);
lean_dec_ref(v_buckets_2603_);
v___y_2590_ = v___y_2600_;
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___x_2611_;
goto v___jp_2589_;
}
}
else
{
size_t v___x_2612_; size_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = ((size_t)0ULL);
v___x_2613_ = lean_usize_of_nat(v___x_2606_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2603_, v___x_2612_, v___x_2613_, v___x_2604_);
lean_dec_ref(v_buckets_2603_);
v___y_2590_ = v___y_2600_;
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___x_2614_;
goto v___jp_2589_;
}
}
}
v___jp_2615_:
{
if (lean_obj_tag(v___y_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_size_2620_; lean_object* v_buckets_2621_; 
v_a_2619_ = lean_ctor_get(v___y_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref(v___y_2618_);
v_size_2620_ = lean_ctor_get(v_a_2619_, 0);
lean_inc(v_size_2620_);
v_buckets_2621_ = lean_ctor_get(v_a_2619_, 1);
lean_inc_ref(v_buckets_2621_);
lean_dec(v_a_2619_);
v___y_2600_ = v___y_2617_;
v___y_2601_ = v___y_2616_;
v_size_2602_ = v_size_2620_;
v_buckets_2603_ = v_buckets_2621_;
goto v___jp_2599_;
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_a_2622_ = lean_ctor_get(v___y_2618_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___y_2618_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___y_2618_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___y_2618_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
v___jp_2630_:
{
lean_object* v_buckets_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_buckets_2634_ = lean_ctor_get(v_results_2543_, 1);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
v___x_2637_ = lean_array_get_size(v_buckets_2634_);
v___x_2638_ = lean_nat_dec_lt(v___x_2635_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_dec(v_sp_2631_);
v___y_2600_ = v___y_2632_;
v___y_2601_ = v___y_2633_;
v_size_2602_ = v___x_2635_;
v_buckets_2603_ = v___x_2636_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_2640_ = lean_nat_dec_le(v___x_2637_, v___x_2637_);
if (v___x_2640_ == 0)
{
if (v___x_2638_ == 0)
{
lean_dec(v_sp_2631_);
v___y_2600_ = v___y_2632_;
v___y_2601_ = v___y_2633_;
v_size_2602_ = v___x_2635_;
v_buckets_2603_ = v___x_2636_;
goto v___jp_2599_;
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = lean_usize_of_nat(v___x_2637_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2544_, v_sp_2631_, v_buckets_2634_, v___x_2641_, v___x_2642_, v___x_2639_, v___y_2632_, v___y_2633_);
v___y_2616_ = v___y_2633_;
v___y_2617_ = v___y_2632_;
v___y_2618_ = v___x_2643_;
goto v___jp_2615_;
}
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2637_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2544_, v_sp_2631_, v_buckets_2634_, v___x_2644_, v___x_2645_, v___x_2639_, v___y_2632_, v___y_2633_);
v___y_2616_ = v___y_2633_;
v___y_2617_ = v___y_2632_;
v___y_2618_ = v___x_2646_;
goto v___jp_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object* v_results_2663_, lean_object* v_useErrorFormat_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
uint8_t v_useErrorFormat_boxed_2668_; lean_object* v_res_2669_; 
v_useErrorFormat_boxed_2668_ = lean_unbox(v_useErrorFormat_2664_);
v_res_2669_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_results_2663_, v_useErrorFormat_boxed_2668_, v_a_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec_ref(v_results_2663_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object* v_n_2670_, lean_object* v_as_2671_, lean_object* v_lo_2672_, lean_object* v_hi_2673_, lean_object* v_w_2674_, lean_object* v_hlo_2675_, lean_object* v_hhi_2676_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2670_, v_as_2671_, v_lo_2672_, v_hi_2673_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object* v_n_2678_, lean_object* v_as_2679_, lean_object* v_lo_2680_, lean_object* v_hi_2681_, lean_object* v_w_2682_, lean_object* v_hlo_2683_, lean_object* v_hhi_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(v_n_2678_, v_as_2679_, v_lo_2680_, v_hi_2681_, v_w_2682_, v_hlo_2683_, v_hhi_2684_);
lean_dec(v_hi_2681_);
lean_dec(v_n_2678_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object* v_00_u03b2_2686_, lean_object* v_m_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2687_, v_a_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object* v_00_u03b2_2690_, lean_object* v_m_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(v_00_u03b2_2690_, v_m_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_m_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object* v_n_2694_, lean_object* v_lo_2695_, lean_object* v_hi_2696_, lean_object* v_hhi_2697_, lean_object* v_pivot_2698_, lean_object* v_as_2699_, lean_object* v_i_2700_, lean_object* v_k_2701_, lean_object* v_ilo_2702_, lean_object* v_ik_2703_, lean_object* v_w_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2696_, v_pivot_2698_, v_as_2699_, v_i_2700_, v_k_2701_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object* v_n_2706_, lean_object* v_lo_2707_, lean_object* v_hi_2708_, lean_object* v_hhi_2709_, lean_object* v_pivot_2710_, lean_object* v_as_2711_, lean_object* v_i_2712_, lean_object* v_k_2713_, lean_object* v_ilo_2714_, lean_object* v_ik_2715_, lean_object* v_w_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(v_n_2706_, v_lo_2707_, v_hi_2708_, v_hhi_2709_, v_pivot_2710_, v_as_2711_, v_i_2712_, v_k_2713_, v_ilo_2714_, v_ik_2715_, v_w_2716_);
lean_dec(v_hi_2708_);
lean_dec(v_lo_2707_);
lean_dec(v_n_2706_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object* v_00_u03b2_2718_, lean_object* v_a_2719_, lean_object* v_x_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2719_, v_x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2722_, lean_object* v_a_2723_, lean_object* v_x_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(v_00_u03b2_2722_, v_a_2723_, v_x_2724_);
lean_dec(v_x_2724_);
lean_dec(v_a_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t v_sz_2726_, size_t v_i_2727_, lean_object* v_bs_2728_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_usize_dec_lt(v_i_2727_, v_sz_2726_);
if (v___x_2729_ == 0)
{
return v_bs_2728_;
}
else
{
lean_object* v_v_2730_; lean_object* v_snd_2731_; lean_object* v_size_2732_; lean_object* v___x_2733_; lean_object* v_bs_x27_2734_; size_t v___x_2735_; size_t v___x_2736_; lean_object* v___x_2737_; 
v_v_2730_ = lean_array_uget_borrowed(v_bs_2728_, v_i_2727_);
v_snd_2731_ = lean_ctor_get(v_v_2730_, 1);
v_size_2732_ = lean_ctor_get(v_snd_2731_, 0);
lean_inc(v_size_2732_);
v___x_2733_ = lean_unsigned_to_nat(0u);
v_bs_x27_2734_ = lean_array_uset(v_bs_2728_, v_i_2727_, v___x_2733_);
v___x_2735_ = ((size_t)1ULL);
v___x_2736_ = lean_usize_add(v_i_2727_, v___x_2735_);
v___x_2737_ = lean_array_uset(v_bs_x27_2734_, v_i_2727_, v_size_2732_);
v_i_2727_ = v___x_2736_;
v_bs_2728_ = v___x_2737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object* v_sz_2739_, lean_object* v_i_2740_, lean_object* v_bs_2741_){
_start:
{
size_t v_sz_boxed_2742_; size_t v_i_boxed_2743_; lean_object* v_res_2744_; 
v_sz_boxed_2742_ = lean_unbox_usize(v_sz_2739_);
lean_dec(v_sz_2739_);
v_i_boxed_2743_ = lean_unbox_usize(v_i_2740_);
lean_dec(v_i_2740_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_boxed_2742_, v_i_boxed_2743_, v_bs_2741_);
return v_res_2744_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0));
v___x_2747_ = l_Lean_stringToMessageData(v___x_2746_);
return v___x_2747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6));
v___x_2756_ = l_Lean_stringToMessageData(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t v_useErrorFormat_2757_, uint8_t v_groupByFilename_2758_, uint8_t v_verbose_2759_, lean_object* v_as_2760_, size_t v_i_2761_, size_t v_stop_2762_, lean_object* v_b_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_a_2768_; lean_object* v_val_2773_; uint8_t v___x_2775_; 
v___x_2775_ = lean_usize_dec_eq(v_i_2761_, v_stop_2762_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v_fst_2777_; lean_object* v_snd_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2841_; 
v___x_2776_ = lean_array_uget(v_as_2760_, v_i_2761_);
v_fst_2777_ = lean_ctor_get(v___x_2776_, 0);
v_snd_2778_ = lean_ctor_get(v___x_2776_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2780_ = v___x_2776_;
v_isShared_2781_ = v_isSharedCheck_2841_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snd_2778_);
lean_inc(v_fst_2777_);
lean_dec(v___x_2776_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2841_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v_warnings_2783_; lean_object* v_size_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_size_2811_ = lean_ctor_get(v_snd_2778_, 0);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = lean_nat_dec_eq(v_size_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
if (v_groupByFilename_2758_ == 0)
{
if (v_useErrorFormat_2757_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2815_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2778_, v___x_2814_, v_useErrorFormat_2757_, v___y_2764_, v___y_2765_);
lean_dec(v_snd_2778_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref(v___x_2815_);
v_warnings_2783_ = v_a_2816_;
goto v___jp_2782_;
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_del_object(v___x_2780_);
lean_dec(v_fst_2777_);
lean_dec_ref(v_b_2763_);
v_a_2817_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2815_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2815_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
goto v___jp_2800_;
}
}
else
{
goto v___jp_2800_;
}
}
else
{
lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2838_; 
lean_del_object(v___x_2780_);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_snd_2778_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2839_ = lean_ctor_get(v_snd_2778_, 1);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_snd_2778_, 0);
lean_dec(v_unused_2840_);
v___x_2826_ = v_snd_2778_;
v_isShared_2827_ = v_isSharedCheck_2838_;
goto v_resetjp_2825_;
}
else
{
lean_dec(v_snd_2778_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2838_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
uint8_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = 2;
v___x_2829_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_verbose_2759_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_del_object(v___x_2826_);
lean_dec(v_fst_2777_);
v_a_2768_ = v_b_2763_;
goto v___jp_2767_;
}
else
{
lean_object* v_toEnvLinter_2830_; lean_object* v_noErrorsFound_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v_toEnvLinter_2830_ = lean_ctor_get(v_fst_2777_, 0);
lean_inc_ref(v_toEnvLinter_2830_);
lean_dec(v_fst_2777_);
v_noErrorsFound_2831_ = lean_ctor_get(v_toEnvLinter_2830_, 1);
lean_inc_ref(v_noErrorsFound_2831_);
lean_dec_ref(v_toEnvLinter_2830_);
v___x_2832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7);
if (v_isShared_2827_ == 0)
{
lean_ctor_set_tag(v___x_2826_, 7);
lean_ctor_set(v___x_2826_, 1, v_noErrorsFound_2831_);
lean_ctor_set(v___x_2826_, 0, v___x_2832_);
v___x_2834_ = v___x_2826_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_noErrorsFound_2831_);
v___x_2834_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v_val_2773_ = v___x_2836_;
goto v___jp_2772_;
}
}
}
}
v___jp_2782_:
{
lean_object* v_toEnvLinter_2784_; lean_object* v_name_2785_; lean_object* v_errorsFound_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v_toEnvLinter_2784_ = lean_ctor_get(v_fst_2777_, 0);
lean_inc_ref(v_toEnvLinter_2784_);
v_name_2785_ = lean_ctor_get(v_fst_2777_, 1);
lean_inc(v_name_2785_);
lean_dec(v_fst_2777_);
v_errorsFound_2786_ = lean_ctor_get(v_toEnvLinter_2784_, 2);
lean_inc_ref(v_errorsFound_2786_);
lean_dec_ref(v_toEnvLinter_2784_);
v___x_2787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1);
v___x_2788_ = l_Lean_MessageData_ofName(v_name_2785_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 7);
lean_ctor_set(v___x_2780_, 1, v___x_2788_);
lean_ctor_set(v___x_2780_, 0, v___x_2787_);
v___x_2790_ = v___x_2780_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2791_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v_errorsFound_2786_);
v___x_2794_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v_warnings_2783_);
v___x_2797_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v_val_2773_ = v___x_2798_;
goto v___jp_2772_;
}
}
v___jp_2800_:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_snd_2778_, v_useErrorFormat_2757_, v___y_2764_, v___y_2765_);
lean_dec(v_snd_2778_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v_warnings_2783_ = v_a_2802_;
goto v___jp_2782_;
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_del_object(v___x_2780_);
lean_dec(v_fst_2777_);
lean_dec_ref(v_b_2763_);
v_a_2803_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2801_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2801_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
}
else
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2763_);
return v___x_2842_;
}
v___jp_2767_:
{
size_t v___x_2769_; size_t v___x_2770_; 
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2761_, v___x_2769_);
v_i_2761_ = v___x_2770_;
v_b_2763_ = v_a_2768_;
goto _start;
}
v___jp_2772_:
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_array_push(v_b_2763_, v_val_2773_);
v_a_2768_ = v___x_2774_;
goto v___jp_2767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object* v_useErrorFormat_2843_, lean_object* v_groupByFilename_2844_, lean_object* v_verbose_2845_, lean_object* v_as_2846_, lean_object* v_i_2847_, lean_object* v_stop_2848_, lean_object* v_b_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
uint8_t v_useErrorFormat_boxed_2853_; uint8_t v_groupByFilename_boxed_2854_; uint8_t v_verbose_boxed_2855_; size_t v_i_boxed_2856_; size_t v_stop_boxed_2857_; lean_object* v_res_2858_; 
v_useErrorFormat_boxed_2853_ = lean_unbox(v_useErrorFormat_2843_);
v_groupByFilename_boxed_2854_ = lean_unbox(v_groupByFilename_2844_);
v_verbose_boxed_2855_ = lean_unbox(v_verbose_2845_);
v_i_boxed_2856_ = lean_unbox_usize(v_i_2847_);
lean_dec(v_i_2847_);
v_stop_boxed_2857_ = lean_unbox_usize(v_stop_2848_);
lean_dec(v_stop_2848_);
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_boxed_2853_, v_groupByFilename_boxed_2854_, v_verbose_boxed_2855_, v_as_2846_, v_i_boxed_2856_, v_stop_boxed_2857_, v_b_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec_ref(v_as_2846_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t v_useErrorFormat_2861_, uint8_t v_groupByFilename_2862_, uint8_t v_verbose_2863_, lean_object* v_as_2864_, lean_object* v_start_2865_, lean_object* v_stop_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0));
v___x_2871_ = lean_nat_dec_lt(v_start_2865_, v_stop_2866_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = lean_array_get_size(v_as_2864_);
v___x_2874_ = lean_nat_dec_le(v_stop_2866_, v___x_2873_);
if (v___x_2874_ == 0)
{
uint8_t v___x_2875_; 
v___x_2875_ = lean_nat_dec_lt(v_start_2865_, v___x_2873_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2870_);
return v___x_2876_;
}
else
{
size_t v___x_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_usize_of_nat(v_start_2865_);
v___x_2878_ = lean_usize_of_nat(v___x_2873_);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2861_, v_groupByFilename_2862_, v_verbose_2863_, v_as_2864_, v___x_2877_, v___x_2878_, v___x_2870_, v___y_2867_, v___y_2868_);
return v___x_2879_;
}
}
else
{
size_t v___x_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_usize_of_nat(v_start_2865_);
v___x_2881_ = lean_usize_of_nat(v_stop_2866_);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2861_, v_groupByFilename_2862_, v_verbose_2863_, v_as_2864_, v___x_2880_, v___x_2881_, v___x_2870_, v___y_2867_, v___y_2868_);
return v___x_2882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object* v_useErrorFormat_2883_, lean_object* v_groupByFilename_2884_, lean_object* v_verbose_2885_, lean_object* v_as_2886_, lean_object* v_start_2887_, lean_object* v_stop_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v_useErrorFormat_boxed_2892_; uint8_t v_groupByFilename_boxed_2893_; uint8_t v_verbose_boxed_2894_; lean_object* v_res_2895_; 
v_useErrorFormat_boxed_2892_ = lean_unbox(v_useErrorFormat_2883_);
v_groupByFilename_boxed_2893_ = lean_unbox(v_groupByFilename_2884_);
v_verbose_boxed_2894_ = lean_unbox(v_verbose_2885_);
v_res_2895_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_boxed_2892_, v_groupByFilename_boxed_2893_, v_verbose_boxed_2894_, v_as_2886_, v_start_2887_, v_stop_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v_stop_2888_);
lean_dec(v_start_2887_);
lean_dec_ref(v_as_2886_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object* v_as_2896_, size_t v_i_2897_, size_t v_stop_2898_, lean_object* v_b_2899_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_usize_dec_eq(v_i_2897_, v_stop_2898_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; 
v___x_2901_ = lean_array_uget_borrowed(v_as_2896_, v_i_2897_);
v___x_2902_ = lean_nat_add(v_b_2899_, v___x_2901_);
lean_dec(v_b_2899_);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_i_2897_, v___x_2903_);
v_i_2897_ = v___x_2904_;
v_b_2899_ = v___x_2902_;
goto _start;
}
else
{
return v_b_2899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object* v_as_2906_, lean_object* v_i_2907_, lean_object* v_stop_2908_, lean_object* v_b_2909_){
_start:
{
size_t v_i_boxed_2910_; size_t v_stop_boxed_2911_; lean_object* v_res_2912_; 
v_i_boxed_2910_ = lean_unbox_usize(v_i_2907_);
lean_dec(v_i_2907_);
v_stop_boxed_2911_ = lean_unbox_usize(v_stop_2908_);
lean_dec(v_stop_2908_);
v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v_as_2906_, v_i_boxed_2910_, v_stop_boxed_2911_, v_b_2909_);
lean_dec_ref(v_as_2906_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object* v_as_2913_, size_t v_i_2914_, size_t v_stop_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_usize_dec_eq(v_i_2914_, v_stop_2915_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_array_uget_borrowed(v_as_2913_, v_i_2914_);
lean_inc(v___x_2920_);
v___x_2921_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v___x_2920_, v___y_2917_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v_a_2924_; uint8_t v___x_2928_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref(v___x_2921_);
v___x_2928_ = lean_unbox(v_a_2922_);
lean_dec(v_a_2922_);
if (v___x_2928_ == 0)
{
v_a_2924_ = v_b_2916_;
goto v___jp_2923_;
}
else
{
lean_object* v___x_2929_; 
lean_inc(v___x_2920_);
v___x_2929_ = lean_array_push(v_b_2916_, v___x_2920_);
v_a_2924_ = v___x_2929_;
goto v___jp_2923_;
}
v___jp_2923_:
{
size_t v___x_2925_; size_t v___x_2926_; 
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2914_, v___x_2925_);
v_i_2914_ = v___x_2926_;
v_b_2916_ = v_a_2924_;
goto _start;
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v_b_2916_);
v_a_2930_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2921_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2921_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_b_2916_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object* v_as_2939_, lean_object* v_i_2940_, lean_object* v_stop_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
size_t v_i_boxed_2945_; size_t v_stop_boxed_2946_; lean_object* v_res_2947_; 
v_i_boxed_2945_ = lean_unbox_usize(v_i_2940_);
lean_dec(v_i_2940_);
v_stop_boxed_2946_ = lean_unbox_usize(v_stop_2941_);
lean_dec(v_stop_2941_);
v_res_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2939_, v_i_boxed_2945_, v_stop_boxed_2946_, v_b_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v_as_2939_);
return v_res_2947_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__0));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__2));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__4));
v___x_2956_ = l_Lean_stringToMessageData(v___x_2955_);
return v___x_2956_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__6));
v___x_2959_ = l_Lean_stringToMessageData(v___x_2958_);
return v___x_2959_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__8));
v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__10));
v___x_2965_ = l_Lean_stringToMessageData(v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__12));
v___x_2968_ = l_Lean_stringToMessageData(v___x_2967_);
return v___x_2968_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__14));
v___x_2971_ = l_Lean_stringToMessageData(v___x_2970_);
return v___x_2971_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__17(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__16));
v___x_2974_ = l_Lean_stringToMessageData(v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object* v_results_2976_, lean_object* v_decls_2977_, uint8_t v_groupByFilename_2978_, lean_object* v_whereDesc_2979_, uint8_t v_scope_2980_, uint8_t v_verbose_2981_, lean_object* v_numLinters_2982_, uint8_t v_useErrorFormat_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_s_2988_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_array_get_size(v_results_2976_);
v___x_2998_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_2983_, v_groupByFilename_2978_, v_verbose_2981_, v_results_2976_, v___x_2996_, v___x_2997_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v_a_3051_; lean_object* v___y_3064_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = lean_array_to_list(v_a_2999_);
v___x_3001_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_3002_ = l_Lean_MessageData_joinSep(v___x_3000_, v___x_3001_);
v___x_3003_ = lean_array_get_size(v_decls_2977_);
v___x_3074_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_3075_ = lean_nat_dec_lt(v___x_2996_, v___x_3003_);
if (v___x_3075_ == 0)
{
v_a_3051_ = v___x_3074_;
goto v___jp_3050_;
}
else
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_nat_dec_le(v___x_3003_, v___x_3003_);
if (v___x_3076_ == 0)
{
if (v___x_3075_ == 0)
{
v_a_3051_ = v___x_3074_;
goto v___jp_3050_;
}
else
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((size_t)0ULL);
v___x_3078_ = lean_usize_of_nat(v___x_3003_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2977_, v___x_3077_, v___x_3078_, v___x_3074_, v_a_2985_);
v___y_3064_ = v___x_3079_;
goto v___jp_3063_;
}
}
else
{
size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = lean_usize_of_nat(v___x_3003_);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2977_, v___x_3080_, v___x_3081_, v___x_3074_, v_a_2985_);
v___y_3064_ = v___x_3082_;
goto v___jp_3063_;
}
}
v___jp_3004_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_inc_ref(v___y_3007_);
v___x_3008_ = l_Lean_stringToMessageData(v___y_3007_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___y_3005_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__5, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_nat_sub(v___x_3003_, v___y_3006_);
v___x_3013_ = l_Nat_reprFast(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
v___x_3015_ = l_Lean_MessageData_ofFormat(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3011_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__7, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Nat_reprFast(v___y_3006_);
v___x_3020_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
v___x_3021_ = l_Lean_MessageData_ofFormat(v___x_3020_);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3018_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__9, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Lean_stringToMessageData(v_whereDesc_2979_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__11, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = l_Nat_reprFast(v_numLinters_2982_);
v___x_3030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
v___x_3031_ = l_Lean_MessageData_ofFormat(v___x_3030_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3028_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__13, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3002_);
v_s_2988_ = v___x_3035_;
goto v___jp_2987_;
}
v___jp_3036_:
{
if (v_verbose_2981_ == 0)
{
lean_dec(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec(v_numLinters_2982_);
lean_dec_ref(v_whereDesc_2979_);
v_s_2988_ = v___x_3002_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3039_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__15, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15);
lean_inc(v___y_3038_);
v___x_3040_ = l_Nat_reprFast(v___y_3038_);
v___x_3041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
v___x_3042_ = l_Lean_MessageData_ofFormat(v___x_3041_);
v___x_3043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3039_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__17, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__17_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__17);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = lean_unsigned_to_nat(1u);
v___x_3047_ = lean_nat_dec_eq(v___y_3038_, v___x_3046_);
lean_dec(v___y_3038_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__18));
v___y_3005_ = v___x_3045_;
v___y_3006_ = v___y_3037_;
v___y_3007_ = v___x_3048_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3049_; 
v___x_3049_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___y_3005_ = v___x_3045_;
v___y_3006_ = v___y_3037_;
v___y_3007_ = v___x_3049_;
goto v___jp_3004_;
}
}
}
v___jp_3050_:
{
lean_object* v___x_3052_; size_t v_sz_3053_; size_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3052_ = lean_array_get_size(v_a_3051_);
lean_dec_ref(v_a_3051_);
v_sz_3053_ = lean_array_size(v_results_2976_);
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_3053_, v___x_3054_, v_results_2976_);
v___x_3056_ = lean_array_get_size(v___x_3055_);
v___x_3057_ = lean_nat_dec_lt(v___x_2996_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_dec_ref(v___x_3055_);
v___y_3037_ = v___x_3052_;
v___y_3038_ = v___x_2996_;
goto v___jp_3036_;
}
else
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_nat_dec_le(v___x_3056_, v___x_3056_);
if (v___x_3058_ == 0)
{
if (v___x_3057_ == 0)
{
lean_dec_ref(v___x_3055_);
v___y_3037_ = v___x_3052_;
v___y_3038_ = v___x_2996_;
goto v___jp_3036_;
}
else
{
size_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_usize_of_nat(v___x_3056_);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_3055_, v___x_3054_, v___x_3059_, v___x_2996_);
lean_dec_ref(v___x_3055_);
v___y_3037_ = v___x_3052_;
v___y_3038_ = v___x_3060_;
goto v___jp_3036_;
}
}
else
{
size_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_usize_of_nat(v___x_3056_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_3055_, v___x_3054_, v___x_3061_, v___x_2996_);
lean_dec_ref(v___x_3055_);
v___y_3037_ = v___x_3052_;
v___y_3038_ = v___x_3062_;
goto v___jp_3036_;
}
}
}
v___jp_3063_:
{
if (lean_obj_tag(v___y_3064_) == 0)
{
lean_object* v_a_3065_; 
v_a_3065_ = lean_ctor_get(v___y_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref(v___y_3064_);
v_a_3051_ = v_a_3065_;
goto v___jp_3050_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v___x_3002_);
lean_dec(v_numLinters_2982_);
lean_dec_ref(v_whereDesc_2979_);
lean_dec_ref(v_results_2976_);
v_a_3066_ = lean_ctor_get(v___y_3064_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___y_3064_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___y_3064_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___y_3064_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_numLinters_2982_);
lean_dec_ref(v_whereDesc_2979_);
lean_dec_ref(v_results_2976_);
v_a_3083_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_2998_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_2998_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
v___jp_2987_:
{
switch(v_scope_2980_)
{
case 0:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__1, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_s_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
case 1:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__3, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v_s_2988_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
default: 
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_s_2988_);
return v___x_2995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object* v_results_3091_, lean_object* v_decls_3092_, lean_object* v_groupByFilename_3093_, lean_object* v_whereDesc_3094_, lean_object* v_scope_3095_, lean_object* v_verbose_3096_, lean_object* v_numLinters_3097_, lean_object* v_useErrorFormat_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
uint8_t v_groupByFilename_boxed_3102_; uint8_t v_scope_boxed_3103_; uint8_t v_verbose_boxed_3104_; uint8_t v_useErrorFormat_boxed_3105_; lean_object* v_res_3106_; 
v_groupByFilename_boxed_3102_ = lean_unbox(v_groupByFilename_3093_);
v_scope_boxed_3103_ = lean_unbox(v_scope_3095_);
v_verbose_boxed_3104_ = lean_unbox(v_verbose_3096_);
v_useErrorFormat_boxed_3105_ = lean_unbox(v_useErrorFormat_3098_);
v_res_3106_ = l_Lean_Linter_EnvLinter_formatLinterResults(v_results_3091_, v_decls_3092_, v_groupByFilename_boxed_3102_, v_whereDesc_3094_, v_scope_boxed_3103_, v_verbose_boxed_3104_, v_numLinters_3097_, v_useErrorFormat_boxed_3105_, v_a_3099_, v_a_3100_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec_ref(v_decls_3092_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_3107_, v_i_3108_, v_stop_3109_, v_b_3110_, v___y_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object* v_as_3115_, lean_object* v_i_3116_, lean_object* v_stop_3117_, lean_object* v_b_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
size_t v_i_boxed_3122_; size_t v_stop_boxed_3123_; lean_object* v_res_3124_; 
v_i_boxed_3122_ = lean_unbox_usize(v_i_3116_);
lean_dec(v_i_3116_);
v_stop_boxed_3123_ = lean_unbox_usize(v_stop_3117_);
lean_dec(v_stop_3117_);
v_res_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(v_as_3115_, v_i_boxed_3122_, v_stop_boxed_3123_, v_b_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec_ref(v_as_3115_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object* v_r_3125_, lean_object* v_k_3126_, lean_object* v_x_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_array_push(v_r_3125_, v_k_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object* v_r_3129_, lean_object* v_k_3130_, lean_object* v_x_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(v_r_3129_, v_k_3130_, v_x_3131_);
lean_dec_ref(v_x_3131_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object* v_f_3133_, lean_object* v_x1_3134_, lean_object* v_x2_3135_, lean_object* v_x3_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_apply_3(v_f_3133_, v_x1_3134_, v_x2_3135_, v_x3_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3138_, lean_object* v_keys_3139_, lean_object* v_vals_3140_, lean_object* v_i_3141_, lean_object* v_acc_3142_){
_start:
{
lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = lean_array_get_size(v_keys_3139_);
v___x_3144_ = lean_nat_dec_lt(v_i_3141_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec(v_i_3141_);
lean_dec(v_f_3138_);
return v_acc_3142_;
}
else
{
lean_object* v_k_3145_; lean_object* v_v_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v_k_3145_ = lean_array_fget_borrowed(v_keys_3139_, v_i_3141_);
v_v_3146_ = lean_array_fget_borrowed(v_vals_3140_, v_i_3141_);
lean_inc(v_f_3138_);
lean_inc(v_v_3146_);
lean_inc(v_k_3145_);
v___x_3147_ = lean_apply_3(v_f_3138_, v_acc_3142_, v_k_3145_, v_v_3146_);
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_nat_add(v_i_3141_, v___x_3148_);
lean_dec(v_i_3141_);
v_i_3141_ = v___x_3149_;
v_acc_3142_ = v___x_3147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3151_, lean_object* v_keys_3152_, lean_object* v_vals_3153_, lean_object* v_i_3154_, lean_object* v_acc_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3151_, v_keys_3152_, v_vals_3153_, v_i_3154_, v_acc_3155_);
lean_dec_ref(v_vals_3153_);
lean_dec_ref(v_keys_3152_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3158_) == 0)
{
lean_object* v_es_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_es_3160_ = lean_ctor_get(v_x_3158_, 0);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_array_get_size(v_es_3160_);
v___x_3163_ = lean_nat_dec_lt(v___x_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_dec(v_f_3157_);
return v_x_3159_;
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_nat_dec_le(v___x_3162_, v___x_3162_);
if (v___x_3164_ == 0)
{
if (v___x_3163_ == 0)
{
lean_dec(v_f_3157_);
return v_x_3159_;
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3162_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3157_, v_es_3160_, v___x_3165_, v___x_3166_, v_x_3159_);
return v___x_3167_;
}
}
else
{
size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = lean_usize_of_nat(v___x_3162_);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3157_, v_es_3160_, v___x_3168_, v___x_3169_, v_x_3159_);
return v___x_3170_;
}
}
}
else
{
lean_object* v_ks_3171_; lean_object* v_vs_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_ks_3171_ = lean_ctor_get(v_x_3158_, 0);
v_vs_3172_ = lean_ctor_get(v_x_3158_, 1);
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3157_, v_ks_3171_, v_vs_3172_, v___x_3173_, v_x_3159_);
return v___x_3174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3175_, lean_object* v_as_3176_, size_t v_i_3177_, size_t v_stop_3178_, lean_object* v_b_3179_){
_start:
{
lean_object* v___y_3181_; uint8_t v___x_3185_; 
v___x_3185_ = lean_usize_dec_eq(v_i_3177_, v_stop_3178_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_array_uget_borrowed(v_as_3176_, v_i_3177_);
switch(lean_obj_tag(v___x_3186_))
{
case 0:
{
lean_object* v_key_3187_; lean_object* v_val_3188_; lean_object* v___x_3189_; 
v_key_3187_ = lean_ctor_get(v___x_3186_, 0);
v_val_3188_ = lean_ctor_get(v___x_3186_, 1);
lean_inc(v_f_3175_);
lean_inc(v_val_3188_);
lean_inc(v_key_3187_);
v___x_3189_ = lean_apply_3(v_f_3175_, v_b_3179_, v_key_3187_, v_val_3188_);
v___y_3181_ = v___x_3189_;
goto v___jp_3180_;
}
case 1:
{
lean_object* v_node_3190_; lean_object* v___x_3191_; 
v_node_3190_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_f_3175_);
v___x_3191_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3175_, v_node_3190_, v_b_3179_);
v___y_3181_ = v___x_3191_;
goto v___jp_3180_;
}
default: 
{
v___y_3181_ = v_b_3179_;
goto v___jp_3180_;
}
}
}
else
{
lean_dec(v_f_3175_);
return v_b_3179_;
}
v___jp_3180_:
{
size_t v___x_3182_; size_t v___x_3183_; 
v___x_3182_ = ((size_t)1ULL);
v___x_3183_ = lean_usize_add(v_i_3177_, v___x_3182_);
v_i_3177_ = v___x_3183_;
v_b_3179_ = v___y_3181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3192_, lean_object* v_as_3193_, lean_object* v_i_3194_, lean_object* v_stop_3195_, lean_object* v_b_3196_){
_start:
{
size_t v_i_boxed_3197_; size_t v_stop_boxed_3198_; lean_object* v_res_3199_; 
v_i_boxed_3197_ = lean_unbox_usize(v_i_3194_);
lean_dec(v_i_3194_);
v_stop_boxed_3198_ = lean_unbox_usize(v_stop_3195_);
lean_dec(v_stop_3195_);
v_res_3199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3192_, v_as_3193_, v_i_boxed_3197_, v_stop_boxed_3198_, v_b_3196_);
lean_dec_ref(v_as_3193_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3200_, lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3200_, v_x_3201_, v_x_3202_);
lean_dec_ref(v_x_3201_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object* v_map_3204_, lean_object* v_f_3205_, lean_object* v_init_3206_){
_start:
{
lean_object* v___f_3207_; lean_object* v___x_3208_; 
v___f_3207_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3207_, 0, v_f_3205_);
v___x_3208_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v___f_3207_, v_map_3204_, v_init_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object* v_map_3209_, lean_object* v_f_3210_, lean_object* v_init_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3209_, v_f_3210_, v_init_3211_);
lean_dec_ref(v_map_3209_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object* v_a_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v_env_3217_; lean_object* v___x_3218_; lean_object* v_map_u2082_3219_; lean_object* v___f_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3216_ = lean_st_ref_get(v_a_3214_);
v_env_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc_ref(v_env_3217_);
lean_dec(v___x_3216_);
v___x_3218_ = l_Lean_Environment_constants(v_env_3217_);
v_map_u2082_3219_ = lean_ctor_get(v___x_3218_, 1);
lean_inc_ref(v_map_u2082_3219_);
lean_dec_ref(v___x_3218_);
v___f_3220_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0));
v___x_3221_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_3222_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_u2082_3219_, v___f_3220_, v___x_3221_);
lean_dec_ref(v_map_u2082_3219_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3224_);
lean_dec(v_a_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule(v_a_3231_, v_a_3232_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object* v_00_u03c3_3235_, lean_object* v_00_u03b2_3236_, lean_object* v_map_3237_, lean_object* v_f_3238_, lean_object* v_init_3239_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3237_, v_f_3238_, v_init_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object* v_00_u03c3_3241_, lean_object* v_00_u03b2_3242_, lean_object* v_map_3243_, lean_object* v_f_3244_, lean_object* v_init_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(v_00_u03c3_3241_, v_00_u03b2_3242_, v_map_3243_, v_f_3244_, v_init_3245_);
lean_dec_ref(v_map_3243_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object* v_map_3247_, lean_object* v_f_3248_, lean_object* v_init_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3248_, v_map_3247_, v_init_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object* v_map_3251_, lean_object* v_f_3252_, lean_object* v_init_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(v_map_3251_, v_f_3252_, v_init_3253_);
lean_dec_ref(v_map_3251_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object* v_00_u03c3_3255_, lean_object* v_00_u03b2_3256_, lean_object* v_map_3257_, lean_object* v_f_3258_, lean_object* v_init_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3258_, v_map_3257_, v_init_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3261_, lean_object* v_00_u03b2_3262_, lean_object* v_map_3263_, lean_object* v_f_3264_, lean_object* v_init_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(v_00_u03c3_3261_, v_00_u03b2_3262_, v_map_3263_, v_f_3264_, v_init_3265_);
lean_dec_ref(v_map_3263_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3267_, lean_object* v_00_u03b1_3268_, lean_object* v_00_u03b2_3269_, lean_object* v_f_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3270_, v_x_3271_, v_x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3274_, lean_object* v_00_u03b1_3275_, lean_object* v_00_u03b2_3276_, lean_object* v_f_3277_, lean_object* v_x_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(v_00_u03c3_3274_, v_00_u03b1_3275_, v_00_u03b2_3276_, v_f_3277_, v_x_3278_, v_x_3279_);
lean_dec_ref(v_x_3278_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3281_, lean_object* v_00_u03b2_3282_, lean_object* v_00_u03c3_3283_, lean_object* v_f_3284_, lean_object* v_as_3285_, size_t v_i_3286_, size_t v_stop_3287_, lean_object* v_b_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3284_, v_as_3285_, v_i_3286_, v_stop_3287_, v_b_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_00_u03b2_3291_, lean_object* v_00_u03c3_3292_, lean_object* v_f_3293_, lean_object* v_as_3294_, lean_object* v_i_3295_, lean_object* v_stop_3296_, lean_object* v_b_3297_){
_start:
{
size_t v_i_boxed_3298_; size_t v_stop_boxed_3299_; lean_object* v_res_3300_; 
v_i_boxed_3298_ = lean_unbox_usize(v_i_3295_);
lean_dec(v_i_3295_);
v_stop_boxed_3299_ = lean_unbox_usize(v_stop_3296_);
lean_dec(v_stop_3296_);
v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3290_, v_00_u03b2_3291_, v_00_u03c3_3292_, v_f_3293_, v_as_3294_, v_i_boxed_3298_, v_stop_boxed_3299_, v_b_3297_);
lean_dec_ref(v_as_3294_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3301_, lean_object* v_00_u03b1_3302_, lean_object* v_00_u03b2_3303_, lean_object* v_f_3304_, lean_object* v_keys_3305_, lean_object* v_vals_3306_, lean_object* v_heq_3307_, lean_object* v_i_3308_, lean_object* v_acc_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3304_, v_keys_3305_, v_vals_3306_, v_i_3308_, v_acc_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3311_, lean_object* v_00_u03b1_3312_, lean_object* v_00_u03b2_3313_, lean_object* v_f_3314_, lean_object* v_keys_3315_, lean_object* v_vals_3316_, lean_object* v_heq_3317_, lean_object* v_i_3318_, lean_object* v_acc_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3311_, v_00_u03b1_3312_, v_00_u03b2_3313_, v_f_3314_, v_keys_3315_, v_vals_3316_, v_heq_3317_, v_i_3318_, v_acc_3319_);
lean_dec_ref(v_vals_3316_);
lean_dec_ref(v_keys_3315_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object* v_x_3321_, lean_object* v_x_3322_){
_start:
{
if (lean_obj_tag(v_x_3322_) == 0)
{
return v_x_3321_;
}
else
{
lean_object* v_key_3323_; lean_object* v_tail_3324_; lean_object* v___x_3325_; 
v_key_3323_ = lean_ctor_get(v_x_3322_, 0);
lean_inc(v_key_3323_);
v_tail_3324_ = lean_ctor_get(v_x_3322_, 2);
lean_inc(v_tail_3324_);
lean_dec_ref(v_x_3322_);
v___x_3325_ = lean_array_push(v_x_3321_, v_key_3323_);
v_x_3321_ = v___x_3325_;
v_x_3322_ = v_tail_3324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object* v_as_3327_, size_t v_i_3328_, size_t v_stop_3329_, lean_object* v_b_3330_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_usize_dec_eq(v_i_3328_, v_stop_3329_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; size_t v___x_3334_; size_t v___x_3335_; 
v___x_3332_ = lean_array_uget_borrowed(v_as_3327_, v_i_3328_);
lean_inc(v___x_3332_);
v___x_3333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(v_b_3330_, v___x_3332_);
v___x_3334_ = ((size_t)1ULL);
v___x_3335_ = lean_usize_add(v_i_3328_, v___x_3334_);
v_i_3328_ = v___x_3335_;
v_b_3330_ = v___x_3333_;
goto _start;
}
else
{
return v_b_3330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object* v_as_3337_, lean_object* v_i_3338_, lean_object* v_stop_3339_, lean_object* v_b_3340_){
_start:
{
size_t v_i_boxed_3341_; size_t v_stop_boxed_3342_; lean_object* v_res_3343_; 
v_i_boxed_3341_ = lean_unbox_usize(v_i_3338_);
lean_dec(v_i_3338_);
v_stop_boxed_3342_ = lean_unbox_usize(v_stop_3339_);
lean_dec(v_stop_3339_);
v_res_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_as_3337_, v_i_boxed_3341_, v_stop_boxed_3342_, v_b_3340_);
lean_dec_ref(v_as_3337_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object* v_a_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v_a_3348_; lean_object* v_env_3349_; lean_object* v___x_3350_; lean_object* v_map_u2081_3351_; lean_object* v_buckets_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3346_ = lean_st_ref_get(v_a_3344_);
v___x_3347_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3344_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
v_env_3349_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_ref(v_env_3349_);
lean_dec(v___x_3346_);
v___x_3350_ = l_Lean_Environment_constants(v_env_3349_);
v_map_u2081_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_ref(v_map_u2081_3351_);
lean_dec_ref(v___x_3350_);
v_buckets_3352_ = lean_ctor_get(v_map_u2081_3351_, 1);
lean_inc_ref(v_buckets_3352_);
lean_dec_ref(v_map_u2081_3351_);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_array_get_size(v_buckets_3352_);
v___x_3355_ = lean_nat_dec_lt(v___x_3353_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_dec_ref(v_buckets_3352_);
lean_dec(v_a_3348_);
return v___x_3347_;
}
else
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_le(v___x_3354_, v___x_3354_);
if (v___x_3356_ == 0)
{
if (v___x_3355_ == 0)
{
lean_dec_ref(v_buckets_3352_);
lean_dec(v_a_3348_);
return v___x_3347_;
}
else
{
lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3366_; 
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; 
v_unused_3367_ = lean_ctor_get(v___x_3347_, 0);
lean_dec(v_unused_3367_);
v___x_3358_ = v___x_3347_;
v_isShared_3359_ = v_isSharedCheck_3366_;
goto v_resetjp_3357_;
}
else
{
lean_dec(v___x_3347_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3366_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
size_t v___x_3360_; size_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = lean_usize_of_nat(v___x_3354_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3352_, v___x_3360_, v___x_3361_, v_a_3348_);
lean_dec_ref(v_buckets_3352_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3362_);
v___x_3364_ = v___x_3358_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3377_; 
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3347_, 0);
lean_dec(v_unused_3378_);
v___x_3369_ = v___x_3347_;
v_isShared_3370_ = v_isSharedCheck_3377_;
goto v_resetjp_3368_;
}
else
{
lean_dec(v___x_3347_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3377_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
size_t v___x_3371_; size_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3371_ = ((size_t)0ULL);
v___x_3372_ = lean_usize_of_nat(v___x_3354_);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3352_, v___x_3371_, v___x_3372_, v_a_3348_);
lean_dec_ref(v_buckets_3352_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3373_);
v___x_3375_ = v___x_3369_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3379_);
lean_dec(v_a_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Linter_EnvLinter_getAllDecls(v_a_3386_, v_a_3387_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object* v_msg_3390_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_panic_fn_borrowed(v___x_3391_, v_msg_3390_);
return v___x_3392_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3396_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2));
v___x_3397_ = lean_unsigned_to_nat(14u);
v___x_3398_ = lean_unsigned_to_nat(22u);
v___x_3399_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1));
v___x_3400_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0));
v___x_3401_ = l_mkPanicMessageWithDecl(v___x_3400_, v___x_3399_, v___x_3398_, v___x_3397_, v___x_3396_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object* v___x_3402_, lean_object* v___x_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
lean_dec_ref(v___x_3403_);
return v_x_3404_;
}
else
{
lean_object* v_key_3406_; lean_object* v_tail_3407_; uint8_t v___x_3408_; lean_object* v___y_3410_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_key_3406_ = lean_ctor_get(v_x_3405_, 0);
lean_inc(v_key_3406_);
v_tail_3407_ = lean_ctor_get(v_x_3405_, 2);
lean_inc(v_tail_3407_);
lean_dec_ref(v_x_3405_);
v___x_3408_ = 0;
lean_inc_ref(v___x_3403_);
v___x_3417_ = l_Lean_Environment_const2ModIdx(v___x_3403_);
v___x_3418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v___x_3417_, v_key_3406_);
lean_dec_ref(v___x_3417_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3);
v___x_3420_ = l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(v___x_3419_);
v___y_3410_ = v___x_3420_;
goto v___jp_3409_;
}
else
{
lean_object* v_val_3421_; 
v_val_3421_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_val_3421_);
lean_dec_ref(v___x_3418_);
v___y_3410_ = v_val_3421_;
goto v___jp_3409_;
}
v___jp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3411_ = lean_box(v___x_3408_);
v___x_3412_ = lean_array_get(v___x_3411_, v___x_3402_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec(v___x_3411_);
v___x_3413_ = lean_unbox(v___x_3412_);
lean_dec(v___x_3412_);
if (v___x_3413_ == 0)
{
lean_dec(v_key_3406_);
v_x_3405_ = v_tail_3407_;
goto _start;
}
else
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_array_push(v_x_3404_, v_key_3406_);
v_x_3404_ = v___x_3415_;
v_x_3405_ = v_tail_3407_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object* v___x_3422_, lean_object* v___x_3423_, lean_object* v_x_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3422_, v___x_3423_, v_x_3424_, v_x_3425_);
lean_dec_ref(v___x_3422_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object* v___x_3427_, lean_object* v___x_3428_, lean_object* v_as_3429_, size_t v_i_3430_, size_t v_stop_3431_, lean_object* v_b_3432_){
_start:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_usize_dec_eq(v_i_3430_, v_stop_3431_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; size_t v___x_3436_; size_t v___x_3437_; 
v___x_3434_ = lean_array_uget_borrowed(v_as_3429_, v_i_3430_);
lean_inc(v___x_3434_);
lean_inc_ref(v___x_3428_);
v___x_3435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3427_, v___x_3428_, v_b_3432_, v___x_3434_);
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3430_, v___x_3436_);
v_i_3430_ = v___x_3437_;
v_b_3432_ = v___x_3435_;
goto _start;
}
else
{
lean_dec_ref(v___x_3428_);
return v_b_3432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object* v___x_3439_, lean_object* v___x_3440_, lean_object* v_as_3441_, lean_object* v_i_3442_, lean_object* v_stop_3443_, lean_object* v_b_3444_){
_start:
{
size_t v_i_boxed_3445_; size_t v_stop_boxed_3446_; lean_object* v_res_3447_; 
v_i_boxed_3445_ = lean_unbox_usize(v_i_3442_);
lean_dec(v_i_3442_);
v_stop_boxed_3446_ = lean_unbox_usize(v_stop_3443_);
lean_dec(v_stop_3443_);
v_res_3447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3439_, v___x_3440_, v_as_3441_, v_i_boxed_3445_, v_stop_boxed_3446_, v_b_3444_);
lean_dec_ref(v_as_3441_);
lean_dec_ref(v___x_3439_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object* v_pkg_3448_, size_t v_sz_3449_, size_t v_i_3450_, lean_object* v_bs_3451_){
_start:
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_usize_dec_lt(v_i_3450_, v_sz_3449_);
if (v___x_3452_ == 0)
{
return v_bs_3451_;
}
else
{
lean_object* v_v_3453_; lean_object* v___x_3454_; lean_object* v_bs_x27_3455_; uint8_t v___x_3456_; size_t v___x_3457_; size_t v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_v_3453_ = lean_array_uget(v_bs_3451_, v_i_3450_);
v___x_3454_ = lean_unsigned_to_nat(0u);
v_bs_x27_3455_ = lean_array_uset(v_bs_3451_, v_i_3450_, v___x_3454_);
v___x_3456_ = l_Lean_Name_isPrefixOf(v_pkg_3448_, v_v_3453_);
lean_dec(v_v_3453_);
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_add(v_i_3450_, v___x_3457_);
v___x_3459_ = lean_box(v___x_3456_);
v___x_3460_ = lean_array_uset(v_bs_x27_3455_, v_i_3450_, v___x_3459_);
v_i_3450_ = v___x_3458_;
v_bs_3451_ = v___x_3460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object* v_pkg_3462_, lean_object* v_sz_3463_, lean_object* v_i_3464_, lean_object* v_bs_3465_){
_start:
{
size_t v_sz_boxed_3466_; size_t v_i_boxed_3467_; lean_object* v_res_3468_; 
v_sz_boxed_3466_ = lean_unbox_usize(v_sz_3463_);
lean_dec(v_sz_3463_);
v_i_boxed_3467_ = lean_unbox_usize(v_i_3464_);
lean_dec(v_i_3464_);
v_res_3468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3462_, v_sz_boxed_3466_, v_i_boxed_3467_, v_bs_3465_);
lean_dec(v_pkg_3462_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object* v_pkg_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v_a_3474_; lean_object* v_env_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v_map_u2081_3478_; lean_object* v_buckets_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3472_ = lean_st_ref_get(v_a_3470_);
v___x_3473_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3470_);
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
v_env_3475_ = lean_ctor_get(v___x_3472_, 0);
lean_inc_ref_n(v_env_3475_, 2);
lean_dec(v___x_3472_);
v___x_3476_ = l_Lean_Environment_header(v_env_3475_);
v___x_3477_ = l_Lean_Environment_constants(v_env_3475_);
v_map_u2081_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc_ref(v_map_u2081_3478_);
lean_dec_ref(v___x_3477_);
v_buckets_3479_ = lean_ctor_get(v_map_u2081_3478_, 1);
lean_inc_ref(v_buckets_3479_);
lean_dec_ref(v_map_u2081_3478_);
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = lean_array_get_size(v_buckets_3479_);
v___x_3482_ = lean_nat_dec_lt(v___x_3480_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_dec_ref(v_buckets_3479_);
lean_dec_ref(v___x_3476_);
lean_dec_ref(v_env_3475_);
lean_dec(v_a_3474_);
return v___x_3473_;
}
else
{
lean_object* v___x_3483_; size_t v_sz_3484_; size_t v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3483_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3476_);
v_sz_3484_ = lean_array_size(v___x_3483_);
v___x_3485_ = ((size_t)0ULL);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3469_, v_sz_3484_, v___x_3485_, v___x_3483_);
v___x_3487_ = lean_nat_dec_le(v___x_3481_, v___x_3481_);
if (v___x_3487_ == 0)
{
if (v___x_3482_ == 0)
{
lean_dec_ref(v___x_3486_);
lean_dec_ref(v_buckets_3479_);
lean_dec_ref(v_env_3475_);
lean_dec(v_a_3474_);
return v___x_3473_;
}
else
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3496_; 
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v___x_3473_, 0);
lean_dec(v_unused_3497_);
v___x_3489_ = v___x_3473_;
v_isShared_3490_ = v_isSharedCheck_3496_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v___x_3473_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3496_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
size_t v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3491_ = lean_usize_of_nat(v___x_3481_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3486_, v_env_3475_, v_buckets_3479_, v___x_3485_, v___x_3491_, v_a_3474_);
lean_dec_ref(v_buckets_3479_);
lean_dec_ref(v___x_3486_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3506_; 
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v___x_3473_, 0);
lean_dec(v_unused_3507_);
v___x_3499_ = v___x_3473_;
v_isShared_3500_ = v_isSharedCheck_3506_;
goto v_resetjp_3498_;
}
else
{
lean_dec(v___x_3473_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3506_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
size_t v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3501_ = lean_usize_of_nat(v___x_3481_);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3486_, v_env_3475_, v_buckets_3479_, v___x_3485_, v___x_3501_, v_a_3474_);
lean_dec_ref(v_buckets_3479_);
lean_dec_ref(v___x_3486_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3502_);
v___x_3504_ = v___x_3499_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object* v_pkg_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3508_, v_a_3509_);
lean_dec(v_a_3509_);
lean_dec(v_pkg_3508_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object* v_pkg_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3512_, v_a_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object* v_pkg_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Linter_EnvLinter_getDeclsInPackage(v_pkg_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_pkg_3517_);
return v_res_3521_;
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
l_Lean_Linter_EnvLinter_instInhabitedLintScope_default = _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope_default();
l_Lean_Linter_EnvLinter_instInhabitedLintScope = _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope();
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
